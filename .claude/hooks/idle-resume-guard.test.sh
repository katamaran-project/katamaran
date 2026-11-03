#!/usr/bin/env bash
# Offline tests for idle-resume-guard.sh: fake transcripts, no API calls.
H=/home/emiel/Documents/katamaran/.claude/hooks/idle-resume-guard.sh
export TMPDIR=$(mktemp -d)
unset CLAUDE_IDLE_GUARD_OFF IDLE_GUARD_MIN IDLE_GUARD_CTX
pass=0; fail=0

ago () { date -u -d "-$1 minutes" +%Y-%m-%dT%H:%M:%S.123Z; }
asst () { # $1 minutes ago, $2 cache_read tokens, $3 uuid
  # Key order mirrors REAL transcripts: message (with its nested "type"s and
  # usage) BEFORE the record's own "type":"assistant" -- an ordered grep once
  # silently allowed everything because of this.
  jq -cn --arg ts "$(ago "$1")" --argjson cr "$2" --arg u "$3" \
    '{parentUuid:"p",message:{model:"m",id:("msg_"+$u),type:"message",role:"assistant",content:[{type:"text",text:"x"}],usage:{input_tokens:2,cache_creation_input_tokens:1000,cache_read_input_tokens:$cr}},type:"assistant",uuid:$u,timestamp:$ts}'
}
userline () { jq -cn --arg t "$1" '{type:"user",message:{content:$t}}'; }

t () { # $1 expect BLOCK|ALLOW, $2 label, $3 transcript, $4 prompt, $5 session
  local json out got r
  json=$(jq -n --arg p "$3" --arg q "$4" --arg s "${5:-s1}" '{transcript_path:$p,prompt:$q,session_id:$s}')
  out=$(printf '%s' "$json" | bash "$H" 2>/dev/null); rc=$?
  if printf '%s' "$out" | grep -q '"block"'; then got=BLOCK; else got=ALLOW; fi
  if [ "$got" = "$1" ] && [ $rc -eq 0 ]; then r="ok  "; pass=$((pass+1)); else r="FAIL"; fail=$((fail+1)); fi
  printf '%s %-5s %s\n' "$r" "$got" "$2"
}
D=$TMPDIR
{ userline hi; asst 130 300000 u1; userline "tool result"; } > $D/idle_big.jsonl
asst 30 300000 u2 > $D/recent_big.jsonl
asst 130 100000 u3 > $D/idle_small.jsonl
{ asst 500 50000 u4; asst 130 400000 u5; userline 'quoted "type":"assistant" text'; } > $D/multi.jsonl
{ asst 130 50000 u6; asst 5 400000 u7; } > $D/last_is_recent.jsonl
echo 'not json at all' > $D/garbage.jsonl

t BLOCK "idle 130 min, 301k context"                 $D/idle_big.jsonl  "continue please" s1
t ALLOW "same prompt resubmitted -> passes"           $D/idle_big.jsonl  "continue please" s1
t BLOCK "other session, same file -> own hold"        $D/idle_big.jsonl  "continue please" s2
t ALLOW "idle 30 min only"                            $D/recent_big.jsonl "go" s3
t ALLOW "context 101k, under threshold"               $D/idle_small.jsonl "go" s4
t ALLOW "slash command /compact"                      $D/idle_big.jsonl  "/compact" s5
t ALLOW "slash command with leading space"            $D/idle_big.jsonl  "  /clear" s6
t BLOCK "uses LAST assistant record (401k, 130 min)"  $D/multi.jsonl     "go" s7
t ALLOW "last record recent even if older one idle"   $D/last_is_recent.jsonl "go" s8
t ALLOW "missing transcript"                          $D/nope.jsonl      "go" s9
t ALLOW "garbage transcript"                          $D/garbage.jsonl   "go" s10
CLAUDE_IDLE_GUARD_OFF=1 t ALLOW "override env"         $D/idle_big.jsonl  "go" s11
IDLE_GUARD_MIN=200 t ALLOW "threshold env respected"   $D/idle_big.jsonl  "go" s12
chmod 000 $TMPDIR 2>/dev/null; t ALLOW "marker not writable -> never block" $D/idle_big.jsonl "go" s13; chmod 700 $TMPDIR

echo "--- sample message ---"
json=$(jq -n --arg p "$D/multi.jsonl" '{transcript_path:$p,prompt:"x",session_id:"sample"}')
printf '%s' "$json" | bash "$H" | jq -r .reason
echo "passed $pass, failed $fail"; [ $fail -eq 0 ]
