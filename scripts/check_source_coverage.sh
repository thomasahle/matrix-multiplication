#!/usr/bin/env bash
# Check that every algebraic-complexity source is compiled by a configured target.
#
# Lake libraries build their configured roots and the imports reachable from
# those roots; merely placing a `.lean` file below a library root does not make
# it part of a build. This static check prevents source files from silently
# falling outside the public libraries and enforcing audit targets.
#
# Two reachability views are checked, and they differ on purpose:
#
#   * the worktree view (every `.lean` under the library roots, tracked or not)
#     keeps in-flight sources honest for the author;
#   * the *tracked* view (`git ls-files`) is what a clean checkout — and therefore
#     CI — actually builds. A tracked file nobody imports is committed source that
#     no gate ever compiles, so it is a hard failure against the grandfather list
#     in `scripts/source_coverage_grandfathered.txt`. That list may only shrink: an
#     entry that has become reachable, or whose file is gone, is reported as a stale
#     notice, while anything *not* on the list fails the build.
#     Regenerate it deliberately with `scripts/check_source_coverage.sh --update`.
set -euo pipefail
cd "$(dirname "$0")/.."

grandfather_file='scripts/source_coverage_grandfathered.txt'
heavy_grandfather_file='scripts/heavy_audit_grandfathered.txt'
update_grandfather_file=0
case "${1:-}" in
  '')
    ;;
  --update)
    update_grandfather_file=1
    ;;
  *)
    echo "usage: $0 [--update]" >&2
    exit 2
    ;;
esac

if ! awk '
    /^\[\[lean_lib\]\]$/ { in_audit = 0 }
    /^name[[:space:]]*=[[:space:]]*"AxiomAudit"[[:space:]]*$/ { in_audit = 1 }
    in_audit && /^globs[[:space:]]*=.*"AxiomAudit[.][*]"/ { found = 1 }
    END { exit !found }
  ' lakefile.toml; then
  echo 'FAIL: source-coverage assumptions require globs = ["AxiomAudit.*"] on the AxiomAudit target.' >&2
  exit 1
fi

if ! awk '
    /^\[\[lean_lib\]\]$/ { in_audit = 0 }
    /^name[[:space:]]*=[[:space:]]*"AxiomAuditCertificate"[[:space:]]*$/ { in_audit = 1 }
    in_audit && /^globs[[:space:]]*=.*"AxiomAuditCertificate[.][*]"/ { found = 1 }
    END { exit !found }
  ' lakefile.toml; then
  echo 'FAIL: source-coverage assumptions require globs = ["AxiomAuditCertificate.*"] on the AxiomAuditCertificate target.' >&2
  exit 1
fi

tracked_sources() {
  if ! command -v git >/dev/null 2>&1 ||
      ! git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    return 0
  fi
  # A tracked path may be missing from the worktree (a deletion not yet
  # committed); such a file cannot be built, and its grandfather entry is
  # reported as stale.
  # `ThirdParty/` is skipped: its libraries set `srcDir = "ThirdParty"`, so a path there is not
  # a module name, and their `X.+` globs make every file below `ThirdParty/X/` a build root, so
  # there is no reachability to check.
  git ls-files -- '*.lean' | while IFS= read -r source; do
    [[ "$source" == ThirdParty/* ]] && continue
    [[ -f "$source" ]] && printf '%s\n' "$source"
  done
}

list_sources() {
  {
    printf '%s\n' \
      AlgebraicComplexity.lean \
      AlgebraicComplexityClients.lean \
      MatrixMultiplication.lean \
      MatrixMultiplicationCertificate.lean \
      AxiomAudit.lean \
      AxiomAuditCertificate.lean
    if command -v rg >/dev/null 2>&1; then
      rg --files AlgebraicComplexity MatrixMultiplication AxiomAudit AxiomAuditCertificate -g '*.lean'
    else
      find AlgebraicComplexity MatrixMultiplication AxiomAudit AxiomAuditCertificate \
        -type f -name '*.lean'
    fi
    # Tracked sources outside those directories — a top-level `.lean` that is not
    # a Lake root, for instance — belong in the graph too.
    tracked_sources
  } | sort -u
}

# Lake library targets, read from the configuration rather than duplicated here: a new
# `[[lean_lib]]` (the `Frontier` statement anchor, for instance) becomes a build root for these
# checks automatically. `globs = ["X.*"]` additionally makes every submodule of `X` its own root.
lake_targets() {
  awk '
    /^\[\[[A-Za-z_]+\]\]/ { section = $0; name = ""; next }
    section != "[[lean_lib]]" { next }
    /^name[[:space:]]*=/ {
      line = $0
      sub(/^name[[:space:]]*=[[:space:]]*"/, "", line)
      sub(/".*$/, "", line)
      name = line
      print "ROOT " name
      next
    }
    /^globs[[:space:]]*=/ {
      if (name != "" && $0 ~ /"[A-Za-z0-9_]+[.][*]"/) {
        print "GLOB " name
      }
    }
  ' lakefile.toml
}

source_to_module() {
  sed -e 's/[.]lean$//' -e 's|/|.|g'
}

modules="$(list_sources | source_to_module | sed -e 's/^/MODULE /')"
targets="$(lake_targets)"
tracked="$(tracked_sources | source_to_module | sed -e 's/^/TRACKED /')"

# Read the complete files so an `import` written inside a nested block comment
# cannot create a false reachability edge. Lean permits nested `/- ... -/`
# comments, so a line-only grep is not a sound approximation here.
import_lines="$(list_sources | xargs awk '
  FNR == 1 { commentDepth = 0 }

  function withoutComments(line,    clean, i, pair) {
    clean = ""
    i = 1
    while (i <= length(line)) {
      pair = substr(line, i, 2)
      if (commentDepth > 0) {
        if (pair == "/-") {
          commentDepth++
          i += 2
        } else if (pair == "-/") {
          commentDepth--
          i += 2
        } else {
          i++
        }
      } else if (pair == "--") {
        break
      } else if (pair == "/-") {
        commentDepth++
        i += 2
      } else {
        clean = clean substr(line, i, 1)
        i++
      }
    }
    return clean
  }

  {
    line = withoutComments($0)
    if (line ~ /^[[:space:]]*((public|private)[[:space:]]+)?import[[:space:]]/) {
      print FILENAME ":" line
      next
    }
    header = line
    gsub(/^[[:space:]]+|[[:space:]]+$/, "", header)
    if (header == "" || header == "module" || header == "prelude") {
      next
    }
    # Imports belong to the Lean module header. Avoid scanning large generated
    # declaration bodies after that header has ended.
    nextfile
  }
' || true)"

# The namespaces that count as project modules are exactly the Lake library targets, so a new
# target needs no edit here either.
project_root_alternation="$(printf '%s\n' "$targets" |
  awk '$1 == "ROOT" { printf "%s%s", separator, $2; separator = "|" }')"

edges="$(printf '%s\n' "$import_lines" | awk -v roots="$project_root_alternation" '
  {
    colon = index($0, ":")
    if (colon == 0) {
      next
    }
    source = substr($0, 1, colon - 1)
    sub(/[.]lean$/, "", source)
    gsub(/\//, ".", source)
    line = substr($0, colon + 1)
    sub(/--.*/, "", line)
    n = split(line, field, /[[:space:]]+/)
    first = 0
    if (field[1] == "import") {
      first = 2
    } else if ((field[1] == "public" || field[1] == "private") && field[2] == "import") {
      first = 3
    }
    for (i = first; first != 0 && i <= n; i++) {
      if (field[i] ~ "^(" roots ")([.][A-Za-z0-9_.]+)?$") {
        print "EDGE", source, field[i]
      }
    }
  }
')"

graph="$modules
$tracked
$targets
$edges"

status=0

if [[ -f "$grandfather_file" ]]; then
  # `grep -v` exits 1 when the list is empty (all comments), which under `set -euo pipefail`
  # would abort the gate exactly when the debt has been fully paid off. `sed` exits 0 either way.
  grandfathered="$(sed -e 's/#.*//' -e 's/[[:space:]]//g' -e '/^$/d' "$grandfather_file" | sort -u)"
else
  grandfathered=''
fi

# Accepted, recorded debt is subtracted from every reachability gate rather than from just one, so
# that the same fact is not both grandfathered and fatal depending on which check notices it.
drop_grandfathered() {
  comm -23 - <(printf '%s\n' "$grandfathered")
}

if [[ -f "$heavy_grandfather_file" ]]; then
  heavy_grandfathered="$(sed -e 's/#.*//' -e 's/[[:space:]]//g' -e '/^$/d' "$heavy_grandfather_file" | sort -u)"
else
  heavy_grandfathered=''
fi


violations="$(printf '%s\n' "$graph" | awk '
  $1 == "MODULE" { module[$2] = 1 }
  $1 == "EDGE" { edge[$2 SUBSEP $3] = 1 }
  $1 == "ROOT" { root[$2] = 1 }
  $1 == "GLOB" { globRoot[$2] = 1 }
  END {
    for (r in root) {
      built[r] = 1
    }
    # A Lake glob makes every submodule of the target its own root, whether or not the
    # compatibility umbrella imports it.
    for (g in globRoot) {
      for (m in module) {
        if (index(m, g ".") == 1) {
          built[m] = 1
        }
      }
    }
    changed = 1
    while (changed) {
      changed = 0
      for (e in edge) {
        split(e, endpoint, SUBSEP)
        source = endpoint[1]
        target = endpoint[2]
        if (built[source] && !built[target]) {
          built[target] = 1
          changed = 1
        }
      }
    }
    for (m in module) {
      if (index(m, "AlgebraicComplexity.") == 1 && !built[m]) {
        print m
      }
    }
  }
' | sort -u | drop_grandfathered)"

if [[ -n "$violations" ]]; then
  echo 'FAIL: Lean sources are not reachable from their public build target:' >&2
  printf '%s\n' "$violations" >&2
  echo 'Import each wanted module from a configured target, add an explicit target glob, or delete superseded source.' >&2
  status=1
fi

# Generated-heavy audits belong in the opt-in certificate target. The accepted placement debt is
# listed in `scripts/heavy_audit_grandfathered.txt`, which is append-blocked and may only shrink;
# a violation that is not listed there fails this gate. Keeping the list in a file rather than in
# an `||` chain inside this awk program is deliberate: the inline version drifted out of date
# twice (its own comment said "seven roots" while naming thirteen, three of which were permits for
# files that had never been committed).
heavy_audit_violations="$(printf '%s\n' "$graph" | awk '
  $1 == "MODULE" { module[$2] = 1 }
  $1 == "EDGE" { edge[$2 SUBSEP $3] = 1 }

  # Not debt, and deliberately not in the file: these two aggregate the whole ordinary closure by
  # construction.  `AxiomAudit.CensusAll` must import everything the audit root reaches, because
  # `#axiom_census` can only see modules it imports; narrowing it would narrow the guarantee.  The
  # bare `AxiomAudit` umbrella is the same story one level up.  Listing either as "debt" would
  # imply a migration that must never happen.
  function byDesign(root) {
    return root == "AxiomAudit.CensusAll" || root == "AxiomAudit"
  }

  END {
    for (m in module) {
      if (index(m, "MatrixMultiplication.Generated.") == 1) {
        reachesGenerated[m] = 1
      }
    }
    changed = 1
    while (changed) {
      changed = 0
      for (e in edge) {
        split(e, endpoint, SUBSEP)
        source = endpoint[1]
        target = endpoint[2]
        if (reachesGenerated[target] && !reachesGenerated[source]) {
          reachesGenerated[source] = 1
          changed = 1
        }
      }
    }
    for (root in module) {
      if ((root == "AxiomAudit" || index(root, "AxiomAudit.") == 1) &&
          reachesGenerated[root] && !byDesign(root)) {
        print root
      }
    }
  }
' | sort)"

# Both sets go through temp files: `grep -v` exits 1 on empty input, which under the
# `set -euo pipefail` at the top of this script would abort the gate exactly when it has nothing
# to report. `sed`, `sort` and `comm` all exit 0 on empty input.
heavy_raw_file="$(mktemp)"
heavy_list_file="$(mktemp)"
printf '%s\n' "$heavy_audit_violations" | sed '/^[[:space:]]*$/d' | sort -u > "$heavy_raw_file"
printf '%s\n' "$heavy_grandfathered" | sed '/^[[:space:]]*$/d' | sort -u > "$heavy_list_file"
stale_heavy_grandfather="$(comm -13 "$heavy_raw_file" "$heavy_list_file")"
heavy_audit_violations="$(comm -23 "$heavy_raw_file" "$heavy_list_file")"
rm -f "$heavy_raw_file" "$heavy_list_file"

if [[ -n "$heavy_audit_violations" ]]; then
  echo 'FAIL: ordinary focused audits newly reach generated certificate data:' >&2
  printf '%s\n' "$heavy_audit_violations" >&2
  echo 'Place generated-heavy checks in AxiomAuditCertificate instead.' >&2
  echo "Only pre-existing debt listed in $heavy_grandfather_file is permitted, and that list may only shrink." >&2
  status=1
fi

# A stale entry means an audit was migrated, so failing on it would fail on the improvement.
if [[ -n "$stale_heavy_grandfather" ]]; then
  echo "NOTICE: $heavy_grandfather_file is stale — $(printf '%s\n' "$stale_heavy_grandfather" | grep -c .) entr(ies) no longer reach generated data." >&2
  echo "        The list may only shrink: remove those lines." >&2
  printf '  %s\n' $stale_heavy_grandfather >&2
fi

# The CW 2.375477 gates below all take that endpoint module as their root. While it is absent from
# the checkout — it is written but not yet committed — they would either pass vacuously (the two
# absence checks) or fail spuriously (the positive proof-spine check), so they are skipped with a
# notice instead of being silently wrong in either direction.
cw_square_endpoint_present=1
# The probe reads `$graph` through a HERE-STRING, not a pipe.  `grep -q` exits the moment it
# matches, so in the pipe form `printf` was killed by SIGPIPE and, under the `set -o pipefail`
# above, the pipeline reported 141 — nonzero — exactly when the module WAS present.  The `!` then
# read that as "absent" and the three gates below were skipped on every run since they were
# written.  A here-string has no second process and no exit status of its own.
if ! grep -qx 'MODULE AlgebraicComplexity.Examples.CoppersmithWinograd2375477' <<<"$graph"; then
  cw_square_endpoint_present=0
  echo 'NOTE: AlgebraicComplexity/Examples/CoppersmithWinograd2375477.lean is not in this checkout;'
  echo '      skipping the three CW 2.375477 boundary and proof-spine gates.'
fi

# The public CW 2.375477 endpoint uses the modern symmetric 64-address value proof.  The historical
# flattened shared-Z route remains an independently audited regression, but importing it through
# the headline theorem would both obscure the proof actually being checked and restore a large,
# unnecessary elaboration cone.  Keep this semantic/performance boundary explicit.
cw_square_legacy_violations="$(printf '%s\n' "$graph" | awk '
  $1 == "MODULE" { module[$2] = 1 }
  $1 == "EDGE" { edge[$2 SUBSEP $3] = 1 }

  function forbidden(m) {
    return m == "AlgebraicComplexity.Examples.CoppersmithWinogradSquareAsymptotic" ||
      m == "AlgebraicComplexity.Examples.CoppersmithWinogradSquareFiniteExtraction" ||
      m == "AlgebraicComplexity.Examples.CoppersmithWinograd112Asymptotic" ||
      m == "AlgebraicComplexity.Examples.CoppersmithWinograd112GlobalCounting" ||
      m == "AlgebraicComplexity.Examples.CoppersmithWinograd112CyclicValue" ||
      m == "AlgebraicComplexity.Examples.CoppersmithWinograd112CyclicValueFormula"
  }

  END {
    root = "AlgebraicComplexity.Examples.CoppersmithWinograd2375477"
    built[root] = 1
    changed = 1
    while (changed) {
      changed = 0
      for (e in edge) {
        split(e, endpoint, SUBSEP)
        source = endpoint[1]
        target = endpoint[2]
        if (built[source] && !built[target]) {
          built[target] = 1
          changed = 1
        }
      }
    }
    for (m in module) {
      if (built[m] && forbidden(m)) {
        print m
      }
    }
  }
' | sort)"

if ((cw_square_endpoint_present == 1)) && [[ -n "$cw_square_legacy_violations" ]]; then
  echo 'FAIL: the modern CW 2.375477 endpoint reaches the legacy flattened extraction:' >&2
  printf '%s\n' "$cw_square_legacy_violations" >&2
  echo 'Move shared declarations to a neutral leaf; keep the flattened route under its focused audit.' >&2
  status=1
fi

# The modern endpoint needs elementary finite reindexing and coupling entropy subadditivity, not
# the much larger two-letter parent-consistency/combination-loss stack.  The lightweight modules
# below are semantic API boundaries, not merely file-size optimizations: a product typed leaf may
# use Coupling and ReindexBasic without acquiring any two-letter compatibility model.
cw_square_probability_boundary_violations="$(printf '%s\n' "$graph" | awk '
  $1 == "MODULE" { module[$2] = 1 }
  $1 == "EDGE" { edge[$2 SUBSEP $3] = 1 }

  function forbidden(m) {
    return m == "AlgebraicComplexity.Probability.Reindex" ||
      m == "AlgebraicComplexity.Probability.TwoLetter" ||
      m == "AlgebraicComplexity.Probability.MarginalProjection" ||
      m == "AlgebraicComplexity.Probability.KullbackLeiblerBounds"
  }

  END {
    root = "AlgebraicComplexity.Examples.CoppersmithWinograd2375477"
    reached[root] = 1
    changed = 1
    while (changed) {
      changed = 0
      for (e in edge) {
        split(e, endpoint, SUBSEP)
        source = endpoint[1]
        target = endpoint[2]
        if ((source in reached) && !(target in reached)) {
          reached[target] = 1
          changed = 1
        }
      }
    }
    for (m in module) {
      if ((m in reached) && forbidden(m)) {
        print m
      }
    }
  }
' | sort)"

if ((cw_square_endpoint_present == 1)) && [[ -n "$cw_square_probability_boundary_violations" ]]; then
  echo 'FAIL: the modern CW 2.375477 endpoint reaches the monolithic two-letter probability stack:' >&2
  printf '%s\n' "$cw_square_probability_boundary_violations" >&2
  echo 'Use Probability.Coupling and Probability.ReindexBasic in ordinary typed-leaf clients.' >&2
  status=1
fi

# Absence checks keep obsolete or over-broad implementations out of the endpoint, but they do not
# by themselves detect an accidental shortcut around a load-bearing mathematical layer.  Keep the
# source-level proof spine explicit as a complementary positive check.  The enforcing axiom audit
# names the principal declarations inside these modules; this check makes sure the public theorem
# still reaches the modern finite extraction, both asymptotic growth stages, the square border-rank
# certificate, and the proved Schönhage/value soundness chain.
cw_square_required_modules_missing="$(printf '%s\n' "$graph" | awk '
  $1 == "MODULE" { module[$2] = 1 }
  $1 == "EDGE" { edge[$2 SUBSEP $3] = 1 }

  function required(m) {
    return m == "AlgebraicComplexity.Examples.CoppersmithWinograd2375477Arithmetic" ||
      m == "AlgebraicComplexity.Examples.CoppersmithWinograd112SymmetricFiniteExtraction" ||
      m == "AlgebraicComplexity.Examples.CoppersmithWinograd112SymmetricGrowth" ||
      m == "AlgebraicComplexity.Examples.CoppersmithWinogradSquareOuterGrowth" ||
      m == "AlgebraicComplexity.Examples.CoppersmithWinogradSquare" ||
      m == "AlgebraicComplexity.MatrixMultiplication.TauValueSoundness" ||
      m == "AlgebraicComplexity.MatrixMultiplication.AsymptoticSum"
  }

  END {
    root = "AlgebraicComplexity.Examples.CoppersmithWinograd2375477"
    reached[root] = 1
    changed = 1
    while (changed) {
      changed = 0
      for (e in edge) {
        split(e, endpoint, SUBSEP)
        source = endpoint[1]
        target = endpoint[2]
        if ((source in reached) && !(target in reached)) {
          reached[target] = 1
          changed = 1
        }
      }
    }
    for (m in module) {
      if (required(m) && !(m in reached)) {
        print m
      }
    }
  }
' | sort)"

if ((cw_square_endpoint_present == 1)) && [[ -n "$cw_square_required_modules_missing" ]]; then
  echo 'FAIL: the modern CW 2.375477 endpoint no longer reaches its declared proof spine:' >&2
  printf '%s\n' "$cw_square_required_modules_missing" >&2
  echo 'Audit any replacement theorem path explicitly before updating this positive dependency gate.' >&2
  status=1
fi

# Finite value producers must not regain the analytic soundness cone through a convenience
# umbrella.  This is both a semantic boundary (constructing a certificate is independent of
# proving its consequence for omega) and a measured elaboration boundary.  The final endpoint is
# deliberately absent from this list: it must import TauValueSoundness and Schönhage's theorem.
finite_value_soundness_violations="$(printf '%s\n' "$graph" | awk '
  $1 == "MODULE" { module[$2] = 1 }
  $1 == "EDGE" { edge[$2 SUBSEP $3] = 1 }

  function finiteRoot(m) {
    return m == "AlgebraicComplexity.MatrixMultiplication.TauValueCore" ||
      m == "AlgebraicComplexity.MatrixMultiplication.TauValueCalculus" ||
      m == "AlgebraicComplexity.MatrixMultiplication.TauValueDirectSum" ||
      m == "AlgebraicComplexity.MatrixMultiplication.TauValueSuperadditivity" ||
      m == "AlgebraicComplexity.MatrixMultiplication.TauValueIndexedDirectSum" ||
      m == "AlgebraicComplexity.MatrixMultiplication.CyclicValueNormalization" ||
      m == "AxiomAudit.TauValueCore" ||
      m == "AlgebraicComplexity.Examples.CoppersmithWinogradSquareTauValueAssembly" ||
      m == "AlgebraicComplexity.Examples.CoppersmithWinogradSquareTauValueGrowth" ||
      m == "AlgebraicComplexity.Examples.CoppersmithWinogradSquare112TauValue"
  }

  function forbidden(m) {
    return m == "AlgebraicComplexity.MatrixMultiplication.TauValue" ||
      m == "AlgebraicComplexity.MatrixMultiplication.TauValueSoundness" ||
      m == "AlgebraicComplexity.MatrixMultiplication.TauValueCyclicSoundness" ||
      m == "AlgebraicComplexity.MatrixMultiplication.AsymptoticSum" ||
      m == "AlgebraicComplexity.Tensor.AsymptoticRankCalculus"
  }

  END {
    for (root in module) {
      if (!finiteRoot(root)) {
        continue
      }
      delete reached
      reached[root] = 1
      changed = 1
      while (changed) {
        changed = 0
        for (e in edge) {
          split(e, endpoint, SUBSEP)
          source = endpoint[1]
          target = endpoint[2]
          if ((source in reached) && !(target in reached)) {
            reached[target] = 1
            changed = 1
          }
        }
      }
      for (m in reached) {
        if (forbidden(m)) {
          print root " -> " m
        }
      }
    }
  }
' | sort)"

if [[ -n "$finite_value_soundness_violations" ]]; then
  echo 'FAIL: a finite value producer reaches the analytic value-soundness cone:' >&2
  printf '%s\n' "$finite_value_soundness_violations" >&2
  echo 'Import TauValueCore in producers; reserve the soundness modules for value-to-omega clients.' >&2
  status=1
fi

# Ordinary Schönhage soundness needs the one-tensor power law for asymptotic rank, but neither the
# structural calculus for external products/direct sums nor the cyclic-certificate adapter.  The
# latter has its own downstream module.  These boundaries keep the ordinary endpoint dependency
# honest and avoid rebuilding unrelated Pascal/rank and cyclic-product proofs.
tau_value_ordinary_soundness_violations="$(printf '%s\n' "$graph" | awk '
  $1 == "MODULE" { module[$2] = 1 }
  $1 == "EDGE" { edge[$2 SUBSEP $3] = 1 }

  function checkedRoot(m) {
    return m == "AlgebraicComplexity.MatrixMultiplication.TauValueSoundness" ||
      m == "AxiomAudit.TauValueSoundness"
  }

  function forbidden(m) {
    return m == "AlgebraicComplexity.Tensor.AsymptoticRankCalculus" ||
      m == "AlgebraicComplexity.MatrixMultiplication.CyclicValueTensor" ||
      m == "AlgebraicComplexity.MatrixMultiplication.TauValueCyclicSoundness"
  }

  END {
    for (root in module) {
      if (!checkedRoot(root)) {
        continue
      }
      delete reached
      reached[root] = 1
      changed = 1
      while (changed) {
        changed = 0
        for (e in edge) {
          split(e, endpoint, SUBSEP)
          source = endpoint[1]
          target = endpoint[2]
          if ((source in reached) && !(target in reached)) {
            reached[target] = 1
            changed = 1
          }
        }
      }
      for (m in reached) {
        if (forbidden(m)) {
          print root " -> " m
        }
      }
    }
  }
' | sort)"

if [[ -n "$tau_value_ordinary_soundness_violations" ]]; then
  echo 'FAIL: ordinary tau-value soundness reaches unrelated rank calculus or cyclic machinery:' >&2
  printf '%s\n' "$tau_value_ordinary_soundness_violations" >&2
  echo 'Use Tensor.AsymptoticRank for the power law and TauValueCyclicSoundness for cyclic adapters.' >&2
  status=1
fi

# The tracked view: what a clean checkout builds.  The check above uses the worktree listing, so
# an untracked in-flight module can make a committed file look reachable when CI would never
# compile it.  Only edges whose *source* is tracked count here.
tracked_orphans="$(printf '%s\n' "$graph" | awk '
  $1 == "MODULE"  { module[$2] = 1 }
  $1 == "TRACKED" { tracked[$2] = 1 }
  $1 == "EDGE"    { edgeSource[NR] = $2; edgeTarget[NR] = $3 }

  $1 == "ROOT" { root[$2] = 1 }
  $1 == "GLOB" { globRoot[$2] = 1 }
  END {
    for (r in root) {
      built[r] = 1
    }
    for (g in globRoot) {
      for (m in tracked) {
        if (index(m, g ".") == 1) {
          built[m] = 1
        }
      }
    }
    for (i in edgeSource) {
      if (edgeSource[i] in tracked) {
        edge[edgeSource[i] SUBSEP edgeTarget[i]] = 1
      }
    }
    changed = 1
    while (changed) {
      changed = 0
      for (e in edge) {
        split(e, endpoint, SUBSEP)
        if (built[endpoint[1]] && !built[endpoint[2]]) {
          built[endpoint[2]] = 1
          changed = 1
        }
      }
    }
    for (m in tracked) {
      if (!built[m]) {
        print m
      }
    }
  }
' | sort)"

if ((update_grandfather_file == 1)); then
  {
    cat <<'HEADER'
# Tracked Lean sources that no configured Lake target reaches.
#
# Every name here is committed source that CI never compiles: its theorems are
# not kernel-checked by any gate, and its `opaque`/generated payloads are not
# reconstructed.  The list exists so that this debt cannot grow silently, and
# `scripts/check_source_coverage.sh` fails both when an unlisted orphan appears
# *and* when an entry here becomes reachable or disappears.  It may only shrink.
#
# To retire an entry: import the module from a configured target (or delete the
# superseded source), then remove its line — or regenerate the whole file with
#
#   scripts/check_source_coverage.sh --update
#
# Do not add a name here to silence a gate on new work; wire the module instead.
#
# Grouping comments below are regenerated mechanically from the module names.
HEADER
    printf '%s\n' "$tracked_orphans" | grep -v '^$' | awk '
      {
        n = split($0, part, /[.]/)
        group = (n >= 3) ? part[1] "." part[2] : part[1]
        if (group != lastGroup) {
          printf "\n# %s\n", group
          lastGroup = group
        }
        print
      }
    '
  } > "$grandfather_file"
  echo "Rewrote $grandfather_file with $(printf '%s\n' "$tracked_orphans" | grep -c . || true) entries."
  exit 0
fi

new_orphans="$(printf '%s\n' "$tracked_orphans" | grep -v '^$' | sort -u | drop_grandfathered)"
stale_grandfather="$(comm -13 <(printf '%s\n' "$tracked_orphans" | grep -v '^$' | sort -u) \
  <(printf '%s\n' "$grandfathered" | grep -v '^$'))"

if [[ -n "$new_orphans" ]]; then
  echo 'FAIL: tracked Lean sources that no configured target reaches (a clean checkout, and therefore CI, never compiles them):' >&2
  printf '%s\n' "$new_orphans" >&2
  echo "Import each from a configured target, delete the superseded source, or — only for accepted debt — list it in $grandfather_file." >&2
  status=1
fi

# A stale entry means the debt shrank, so failing on it would be failing on an improvement — and in
# a tree where several parties commit umbrella wiring in parallel, it would fail on *their* commit
# rather than on the one that introduced anything. It is a loud notice instead, and the list is
# still append-blocked by the check above, so the debt can only move one way.
if [[ -n "$stale_grandfather" ]]; then
  echo "NOTICE: $grandfather_file is stale — $(printf '%s\n' "$stale_grandfather" | grep -c .) entr(ies) are now reachable or gone." >&2
  echo "        The list may only shrink: remove those lines, or run 'scripts/check_source_coverage.sh --update'." >&2
  printf '  %s\n' $stale_grandfather >&2
fi

# The axiom census is only as strong as its import closure, so the closure must equal the build.
# A library module that a target builds but no census client imports is a hole in the trust policy:
# `#axiom_census` would never see its declarations.
census_gaps="$(printf '%s\n' "$graph" | awk '
  $1 == "TRACKED" { module[$2] = 1 }
  $1 == "ROOT" { root[$2] = 1 }
  $1 == "GLOB" { globRoot[$2] = 1 }
  $1 == "EDGE" { edgeSource[NR] = $2; edgeTarget[NR] = $3 }

  # Everything a target builds except the two audit trees.  The audit modules hold
  # `#assert_axioms`/`#assert_statement_fingerprint` commands rather than declarations, and there
  # are two hundred of them; every other built module carries mathematics that must be censused.
  function isLibrary(m) {
    return !(m == "AxiomAudit" || index(m, "AxiomAudit.") == 1 ||
      m == "AxiomAuditCertificate" || index(m, "AxiomAuditCertificate.") == 1)
  }

  function closeReach(seed,    changed, e, endpoint) {
    changed = 1
    while (changed) {
      changed = 0
      for (e in edge) {
        split(e, endpoint, SUBSEP)
        if ((endpoint[1] in seed) && !(endpoint[2] in seed)) {
          seed[endpoint[2]] = 1
          changed = 1
        }
      }
    }
  }

  END {
    if (!("AxiomAudit.CensusAll" in module) || !("AxiomAuditCertificate.Census" in module) \
        || !("AxiomAuditCertificate.CensusQ20" in module)) {
      print "MISSING-CENSUS-CLIENT"
      exit
    }
    # Tracked view only: a clean checkout is what CI builds and censuses, and an untracked
    # in-flight audit root would otherwise appear to build library modules the census cannot see.
    for (i in edgeSource) {
      if (edgeSource[i] in module) {
        edge[edgeSource[i] SUBSEP edgeTarget[i]] = 1
      }
    }
    # Required scope: the *library* targets. A Lake glob target (`AxiomAudit.*`,
    # `AxiomAuditCertificate.*`) is a bag of two hundred audit files, and requiring the census to
    # import each of them would make this gate unsatisfiable rather than informative; a library
    # module that only some focused audit reaches is reported below as a notice instead.
    for (r in root) {
      if (!(r in globRoot)) {
        built[r] = 1
      }
    }
    closeReach(built)
    censused["AxiomAudit.CensusAll"] = 1
    censused["AxiomAuditCertificate.Census"] = 1
    censused["AxiomAuditCertificate.CensusQ20"] = 1
    # The root of the opt-in `OpenAIBridge` target is its own census client: it runs
    # `#axiom_census_roots` over the bridge and the vendored developments it imports.  The
    # ordinary census must not import vendored code, so it cannot be the one to cover that target.
    if ("OpenAIBridge" in module) {
      censused["OpenAIBridge"] = 1
    }
    closeReach(censused)
    for (m in module) {
      if ((m in built) && isLibrary(m) && !(m in censused)) {
        print m
      }
    }
    # Not fatal, but worth seeing: modules no library target reaches, built only because a focused
    # audit imports them, and therefore outside every census closure.
    for (g in globRoot) {
      for (m in module) {
        if (index(m, g ".") == 1) {
          auditRoot[m] = 1
        }
      }
    }
    for (m in auditRoot) {
      auditReach[m] = 1
    }
    closeReach(auditReach)
    for (m in module) {
      if ((m in auditReach) && !(m in built) && isLibrary(m) && !(m in censused)) {
        print "NOTICE " m
      }
    }
  }
' | sort)"

if [[ "$census_gaps" == 'MISSING-CENSUS-CLIENT' ]]; then
  echo 'FAIL: the enforcing axiom census clients are missing (expected AxiomAudit/CensusAll.lean, AxiomAuditCertificate/Census.lean and AxiomAuditCertificate/CensusQ20.lean).' >&2
  echo 'They are the authority for the trust policy in DESIGN.md; do not delete them.' >&2
  status=1
else
  census_notices="$(printf '%s\n' "$census_gaps" | sed -n 's/^NOTICE //p')"
  census_failures="$(printf '%s\n' "$census_gaps" | grep -v '^NOTICE ' | grep -v '^$' || true)"
  if [[ -n "$census_failures" ]]; then
    echo 'FAIL: library-target modules are built but not covered by any #axiom_census closure:' >&2
    printf '%s\n' "$census_failures" >&2
    echo 'Import them (directly or transitively) from AxiomAudit/CensusAll.lean, AxiomAuditCertificate/Census.lean or AxiomAuditCertificate/CensusQ20.lean (or, for the OpenAIBridge target, its root OpenAIBridge.lean).' >&2
    status=1
  fi
  if [[ -n "$census_notices" ]]; then
    echo "NOTICE: $(printf '%s\n' "$census_notices" | grep -c .) module(s) are built only because a focused audit imports them," >&2
    echo '        so no #axiom_census closure covers them. Wire them into a library target:' >&2
    printf '  %s\n' $census_notices >&2
  fi
fi

if ((status == 0)); then
  echo 'Source coverage, the modern CW 2.38 boundary, and the finite-value/soundness boundary are clean; seven generated-heavy audit roots are explicitly grandfathered.'
  echo "Every library module built by a configured target is inside an #axiom_census closure; $(printf '%s\n' "$grandfathered" | grep -c . || true) tracked sources remain grandfathered as unreachable."
fi

exit "$status"
