set -e
set -u

ISABELLE=isabelle
MASH_STATE="$(isabelle getenv -b ISABELLE_HOME_USER)/mash_state"

for a in Benchmarks.int.*
do
    echo $a
    cp $a Benchmarks.thy
    [[ ! -f "$MASH_STATE" ]] || rm "$MASH_STATE"
    [ -d "mirabelle.$a.all"  ] || "$ISABELLE" mirabelle -d ~/Work/Isabelle/afp-2026-02-09/thys/Word_Lib/ -d ~/Work/Isabelle/afp-2026-02-09/thys/IEEE_Floating_Point/ -d . -T Benchmarks -O "mirabelle.$a.all" -A "flattening [keep_probs=true]" IEEE_Floating_Point_Evaluation

done
