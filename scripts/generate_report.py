import json
from collections import defaultdict

def summarize():
    records = []
    with open("benchmarks/results.jsonl") as f:
        for line in f:
            if line.strip():
                records.append(json.loads(line))

    by_mod = defaultdict(list)
    for r in records:
        by_mod[r["module"]].append(r)

    print("| Lean 4 Module | Attempts | Final Status | Avg Compile (ms) | Best Compile (ms) |")
    print("| :--- | :---: | :---: | :---: | :---: |")
    for mod, runs in by_mod.items():
        attempts = len(runs)
        passed = any(r["success"] for r in runs)
        avg_ms = round(sum(r["compile_ms"] for r in runs) / attempts, 1)
        best_ms = min(r["compile_ms"] for r in runs if r["success"]) if passed else "-"
        status = "PASS (0 sorry)" if passed else "IN PROGRESS"
        print(f"| `{mod}` | {attempts} | **{status}** | {avg_ms} ms | {best_ms} ms |")

if __name__ == "__main__":
    summarize()
