#!/bin/bash
# SessionStart hook: 現ブランチの derivation path と未完了 TODO を context に注入する。
# CLAUDE.md には書けない「毎回変わる情報」だけをここで出す。
cd "$(git rev-parse --show-toplevel 2>/dev/null)" || exit 0

BR=$(git branch --show-current 2>/dev/null)
[ -z "$BR" ] && exit 0

{
  # --- ブランチ位置 ---
  if [ "$BR" = "main" ]; then
    echo "[branch] main"
  else
    # 左 = BR にしかない commit (= ahead), 右 = main にしかない commit (= behind)
    read -r AHEAD BEHIND < <(git rev-list --left-right --count "$BR...main" 2>/dev/null)
    echo "[branch] $BR  (main に対して ${AHEAD:-?} ahead / ${BEHIND:-?} behind)"
  fi

  # --- README の最新 derivation path ---
  SECTION=$(awk '/^## Derivation path/{f=1;next} f&&/^### /{sub(/^### /,"");print;exit}' README.md)
  RAW=$(awk '/^## Derivation path/{f=1;next} f&&/^### /{s=1;next} s&&/^- /{sub(/^- /,"");print;exit}' README.md)

  if [ -n "$RAW" ]; then
    echo "[path]   最新セクション \"$SECTION\""
    FOUND=() MISSING=()
    # "eval1a, 1b_{1,2,3}, 4{b,c}" 形式。区切りは ", " で、brace 内の "," には空白がない。
    for tok in $(echo "$RAW" | sed 's/, / /g' | tr -cd 'a-zA-Z0-9_{}, \n'); do
      tok="${tok/#Eval/eval}"   # main の README は "Eval1a, ..." と先頭大文字
      case "$tok" in eval*) ;; *) tok="eval$tok" ;; esac
      # 括弧内の注釈語 ("dummy" 等) が混ざるので eval<数字> だけ通す
      [[ "$tok" =~ ^eval[0-9] ]] || continue
      for d in $(eval "echo $tok" 2>/dev/null); do
        if [ -d "$d" ]; then FOUND+=("$d"); else MISSING+=("$d"); fi
      done
    done
    echo "         ${FOUND[*]}"
    [ ${#MISSING[@]} -gt 0 ] && echo "         !! README に載っているが実在しない: ${MISSING[*]}"

    # --- パス上のフォルダに残る未完了マーカー ---
    if [ ${#FOUND[@]} -gt 0 ]; then
      HITS=$(grep -nE '\(\*.*(すべき|べきところ|TODO|残課題|未解決|直す|詰む|うまく行っ|したい|ではないか)' \
               "${FOUND[@]/%//eval.ml}" 2>/dev/null | head -10)
      if [ -n "$HITS" ]; then
        echo "[todo]   パス上に残る未完了マーカー（表示のみ・着手判断はしない）:"
        echo "$HITS" | sed 's/^/         /'
      fi
    fi
  else
    echo "[path]   README から derivation path を抽出できなかった。README.md を直接読むこと。"
  fi

  # --- 直近の作業 ---
  echo "[recent]"
  git log -3 --format='%h %s' | sed 's/^/         /'
  DIRTY=$(git status --porcelain --untracked-files=no | head -5)
  if [ -n "$DIRTY" ]; then
    echo "[dirty]"
    echo "$DIRTY" | sed 's/^/         /'
  fi

  echo "[rule]   導出は必ず「前ステップからの自明な変換」のみ。詳細は CLAUDE.md を参照。"
} 2>/dev/null
