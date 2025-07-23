import os
import re
import subprocess
from concurrent.futures import ThreadPoolExecutor, as_completed
from collections import defaultdict, deque

AGDA_CMD = ["agda", "-v0"]  # Adjust options as needed

IMPORT_RE = re.compile(r"^\s*(open )?import\s+([A-Za-z0-9_.]+)")

IGNORE = ["./coverings.agda", "./test.agda"]

def module_name_to_path(modname: str, root: str) -> str:
    """Convert a module name to a file path, if it exists."""
    if modname.startswith("Cubical.") or modname.startswith("Agda."):
        return None
    path = os.path.join(root, *modname.split(".")) + ".agda"
    return path if os.path.exists(path) else None

def parse_dependencies(filepath, root):
    deps = []
    with open(filepath, encoding="utf-8") as f:
        for line in f:
            m = IMPORT_RE.match(line)
            if m:
                modname = m.group(2)
                dep_path = module_name_to_path(modname, root)
                if dep_path:
                    deps.append(dep_path)
    return deps

def find_agda_files(root):
    return [
        os.path.join(dp, f)
        for dp, _, filenames in os.walk(root)
        for f in filenames
        if f.endswith(".agda") and not f.startswith("Cubical.") and not f.startswith("Agda.")
    ]

def build_dependency_graph(files, root):
    graph = defaultdict(list)
    reverse_graph = defaultdict(set)
    for file in files:
        if file in IGNORE: continue

        deps = parse_dependencies(file, root)
        graph[file] = deps
        for dep in deps:
            reverse_graph[dep].add(file)
    return graph, reverse_graph

def run_agda(filepath):
    try:
        print(f"? Compiling {filepath}")
        subprocess.run(AGDA_CMD + [filepath], check=True)
        print(f"? Compiled {filepath}")
        return True
    except subprocess.CalledProcessError:
        print(f"? Failed {filepath}")
        return False

def schedule_build(graph, reverse_graph, num_workers=8):
    pending_deps = {file: len(deps) for file, deps in graph.items()}
    ready = deque([file for file, count in pending_deps.items() if count == 0])
    completed = set()

    with ThreadPoolExecutor(max_workers=num_workers) as executor:
        futures = {}

        while ready or futures:
            # Submit all ready tasks
            while ready:
                file = ready.popleft()
                futures[executor.submit(run_agda, file)] = file

            # Wait for any to complete
            done, _ = as_completed(futures), []
            for future in done:
                file = futures.pop(future)
                if future.result():
                    completed.add(file)
                    # Update reverse dependencies
                    for dependent in reverse_graph[file]:
                        pending_deps[dependent] -= 1
                        if pending_deps[dependent] == 0:
                            ready.append(dependent)

def main(root_dir):
    files = find_agda_files(root_dir)
    graph, reverse_graph = build_dependency_graph(files, root_dir)
    schedule_build(graph, reverse_graph, num_workers=os.cpu_count())

if __name__ == "__main__":
    import sys
    if len(sys.argv) != 2:
        print("Usage: python check.py <directory>")
    else:
        main(sys.argv[1])
