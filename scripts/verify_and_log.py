import subprocess, sys, time, json
from datetime import datetime, timezone

def verify(module: str, file_path: str, model_tag: str = "claude-app"):
    t0 = time.time()
    proc = subprocess.run(["lake", "build", module], capture_output=True, text=True)
    ms = round((time.time() - t0) * 1000, 1)
    out = (proc.stdout + "\n" + proc.stderr).strip()
    has_sorry = "declaration uses 'sorry'" in out
    success = (proc.returncode == 0) and not has_sorry

    record = {
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "model": model_tag,
        "module": module,
        "file": file_path,
        "success": success,
        "has_sorry": has_sorry,
        "compile_ms": ms,
        "error_tail": "" if success else out[-800:]
    }
    with open("benchmarks/results.jsonl", "a") as f:
        f.write(json.dumps(record) + "\n")

    print(f"[{'PASS' if success else 'FAIL'}] {module} ({ms} ms)")
    if not success:
        print(out)
        sys.exit(1)

if __name__ == "__main__":
    mod = sys.argv[1]
    fpath = sys.argv[2]
    tag = sys.argv[3] if len(sys.argv) > 3 else "claude-app"
    verify(mod, fpath, tag)
