#!/bin/bash
# Stop hook: check if sorry-filling task is complete.
# Reads sorry-scope.txt for scoped files. Supports "dep:" prefix for dependency files.
# If no scope file exists, checks all of HeckeRIngs/.

PROJECT_DIR="${CLAUDE_PROJECT_DIR:-/Users/mcu22seu/Documents/GitHub/LeanModularForms-hecke}"
SCOPE_FILE="$PROJECT_DIR/.claude/hooks/sorry-scope.txt"

count_sorries() {
  local target="$1"
  local results=""
  if [ -f "$target" ]; then
    results=$(grep -Hn '^\s*sorry\b\|· sorry\| sorry$' "$target" 2>/dev/null \
      | grep -v '^\s*--' \
      | grep -v 'sorry-free\|no sorry\|sorry_analyzer\|-- .*sorry')
  elif [ -d "$target" ]; then
    results=$(grep -rn --include='*.lean' '^\s*sorry\b\|· sorry\| sorry$' "$target" 2>/dev/null \
      | grep -v '^\s*--' \
      | grep -v 'sorry-free\|no sorry\|sorry_analyzer\|-- .*sorry')
  fi
  echo "$results"
}

DIRECT_TARGETS=""
DEP_TARGETS=""

if [ -f "$SCOPE_FILE" ]; then
  while IFS= read -r line; do
    [ -z "$line" ] && continue
    [[ "$line" == \#* ]] && continue
    if [[ "$line" == dep:* ]]; then
      path="${line#dep:}"
      [[ "$path" != /* ]] && path="$PROJECT_DIR/$path"
      DEP_TARGETS="$DEP_TARGETS $path"
    else
      [[ "$line" != /* ]] && line="$PROJECT_DIR/$line"
      DIRECT_TARGETS="$DIRECT_TARGETS $line"
    fi
  done < "$SCOPE_FILE"
else
  DIRECT_TARGETS="$PROJECT_DIR/LeanModularForms/HeckeRIngs"
fi

# Count direct sorries
DIRECT_COUNT=0
DIRECT_LOCS=""
for target in $DIRECT_TARGETS; do
  results=$(count_sorries "$target")
  if [ -n "$results" ]; then
    c=$(echo "$results" | wc -l | tr -d ' ')
    DIRECT_COUNT=$((DIRECT_COUNT + c))
    DIRECT_LOCS="${DIRECT_LOCS}$(echo "$results" | sed "s|$PROJECT_DIR/||")
"
  fi
done

# Count dependency sorries
DEP_COUNT=0
DEP_LOCS=""
for target in $DEP_TARGETS; do
  results=$(count_sorries "$target")
  if [ -n "$results" ]; then
    c=$(echo "$results" | wc -l | tr -d ' ')
    DEP_COUNT=$((DEP_COUNT + c))
    DEP_LOCS="${DEP_LOCS}$(echo "$results" | sed "s|$PROJECT_DIR/||")
"
  fi
done

TOTAL=$((DIRECT_COUNT + DEP_COUNT))

if [ "$TOTAL" -eq 0 ]; then
  echo '{"decision": "allow", "reason": "All sorries (direct + dependencies) are filled! Great work."}'
  exit 0
fi

# Trim locations
DIRECT_LOCS=$(echo "$DIRECT_LOCS" | grep -v '^$' | head -10)
DEP_LOCS=$(echo "$DEP_LOCS" | grep -v '^$' | head -10)

# Identify relevant plan files
PLANS=""
ALL_LOCS="$DIRECT_LOCS $DEP_LOCS"
if echo "$ALL_LOCS" | grep -qi 'CongruenceHecke'; then
  PLANS="docs/plans/tickets-congruence-hecke.md, docs/plans/tickets-remaining-sorries.md"
fi
if echo "$ALL_LOCS" | grep -qi 'HeckeT_p\|Gamma1Pair\|DiamondOp\|LevelEmbed'; then
  PLANS="${PLANS:+$PLANS, }docs/plans/strong-multiplicity-one.md"
fi
if echo "$ALL_LOCS" | grep -qi 'GL2\|GLn'; then
  PLANS="${PLANS:+$PLANS, }docs/plans/2026-03-06-hecke-ring-theorem-3-24.md"
fi
[ -z "$PLANS" ] && PLANS="docs/plans/tickets-congruence-hecke.md"

# Build context sections
DIRECT_SEC=""
if [ "$DIRECT_COUNT" -gt 0 ]; then
  ESCAPED_D=$(echo "$DIRECT_LOCS" | perl -pe 'chomp if eof; s/\n/\\n/g; s/"/\\"/g')
  DIRECT_SEC="Direct target sorries ($DIRECT_COUNT):\\n$ESCAPED_D"
fi

DEP_SEC=""
if [ "$DEP_COUNT" -gt 0 ]; then
  ESCAPED_DEP=$(echo "$DEP_LOCS" | perl -pe 'chomp if eof; s/\n/\\n/g; s/"/\\"/g')
  DEP_SEC="Dependency sorries ($DEP_COUNT) — these block your targets:\\n$ESCAPED_DEP"
fi

python3 -c "
import json
sections = []
d = '$DIRECT_SEC'
dep = '$DEP_SEC'
if d: sections.append(d)
if dep: sections.append(dep)
sorry_detail = '\\n\\n'.join(sections)

ctx = (
    'STOP HOOK: You still have $TOTAL sorry(s) remaining ($DIRECT_COUNT direct, $DEP_COUNT dependencies). DO NOT STOP.\\n\\n'
    + sorry_detail + '\\n\\n'
    'Check these plan references: $PLANS\\n\\n'
    'Action plan:\\n'
    '1. Start with dependency sorries first (they block downstream work)\\n'
    '2. Read the relevant plan file to find the proof outline\\n'
    '3. Use lean_goal / lean_hover_info to understand the sorry context\\n'
    '4. Fill the sorry and verify with lean_diagnostic_messages\\n'
    '5. Then move to direct target sorries\\n'
    '6. Keep going until all sorries are filled'
)
print(json.dumps({
    'decision': 'block',
    'reason': 'There are still $TOTAL sorry(s) remaining ($DIRECT_COUNT direct + $DEP_COUNT deps). Task is not complete.',
    'hookSpecificOutput': {
        'hookEventName': 'Stop',
        'additionalContext': ctx
    }
}))
"
