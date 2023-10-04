# a program that counts various kinds of lines in a Vale file.

from collections import defaultdict
import os
import re
from pathlib import Path
from typing import List
import sys

# Records the bodies of each procedure.
# maps each procedure to a pair (header, list_of_code_lines)
procedure_body = {}

def count_non_comment_lines(filename):
    """Count the number of non-comment lines in a file."""
    with open(filename) as f:
        return len([line for line in f if line.strip() and not line.strip().startswith("//")])
    
def count_non_blank_lines(filename):
    """Count the number of non-blank lines in a file."""
    with open(filename) as f:
        return len([line for line in f if line.strip()])

def count_lines(filename):
    """Count the number of lines in a file."""
    with open(filename) as f:
        return len(f.readlines())

def parse_formal(param):
    """Parse a formal parameter and return the name and type."""
    if param.startswith("inline"):
        param = param[6:].strip()
    colon = param.find(":")
    name = param[:colon]
    type = param[colon+1:]
    return (name, type)

def parse_procedure_hdr(line):
    """Parse a procedure header line and return the name and formals."""
    hdr = line[9:].strip()  # remove "procedure"
    br1 = hdr.find("(")
    br2 = hdr.find(")")
    name = hdr[:br1]
    formals = [parse_formal(s.strip()) for s in hdr[br1+1:br2].split(",") if s]
    return (name, formals)

def parse_procedure_call(line):
    """Parse a procedure call and return the name and arguments."""
    br1 = line.find("(")
    br2 = line.find(")")
    name = line[:br1]
    args = [s.strip() for s in line[br1+1:br2].split(",") if s]
    return (name, args)

def strip_asserts(code):
    """Remove all assert, assume and lemma statements from code."""
    out = []
    in_assert = False
    for line in code:
        if line.startswith("assert") or line.startswith("assume") or line.startswith("lemma_"):
            in_assert = True
        if not in_assert:
            out.append(line)
        if in_assert and line.endswith(";"):
            in_assert = False
    return out

assert strip_asserts(["ADD", "assert x == 0;", "SUB"]) == ["ADD", "SUB"]
assert strip_asserts(["assert x == 0 &&", "y == 1;"]) == []
assert strip_asserts(["lemma_cons_tail_eq();", "EQ()"]) == ["EQ()"]

def strip_all_asserts():
    """Remove all assert statements from all procedures."""
    for p in procedure_body:
        (formals, body) = procedure_body[p]
        procedure_body[p] = (formals, strip_asserts(body))

def is_evm(call):
    """True if the call is an EVM instruction (all uppercase).
    TODO: add Safe_Return and SafeRevert?  See EVM.Vale.Inx_Basic.vaf.
    """
    return re.match("[A-Z][A-Z][A-Z_0-9]*\(.*\);", call)

assert is_evm("ADD();")
assert is_evm("PUSH(value);")
assert not is_evm("Add_value(offset);")

def is_call(line):
    """True if the line of code is a call to a helper procedure (not all uppercase)."""
    return re.match("[A-Za-z][a-z][a-zA-Z0-9_]*\(.*\);", line)

assert is_call("overflowCheck();")
assert is_call("Add_two_values(receiver_address, offset);")
assert not is_call("PUSH(value)")

def get_flattened_code(body:List[str], argtypes, actuals) -> List[str]:
    """Flatten a list of code lines into a single string."""
    out = []
    for line in body:
        if is_call(line):
            (name, args) = parse_procedure_call(line)
            (formals, body) = procedure_body[name]
            out.extend(get_flattened_code(body, formals, args))
        elif is_evm(line):
            (name, args) = parse_procedure_call(line)
            out.append(f"{name} {' '.join(args)}".strip())
        else:
            out.append(line)
    return out

def count_line_types(filename):
    """Count the number of different kinds of lines in a file."""
    key = "global"
    counts = defaultdict(int)
    current_proc = ""  # current procedure name
    with open(filename) as f:
        for line in f:
            contents = line.strip()
            if contents == "":
                counts["blank"] += 1
            elif contents.startswith("//"):
                counts["comment"] += 1
            elif contents.startswith("procedure"):
                counts["procedure"] += 1
                key = "specification"  # following lines
                current_proc, formals = parse_procedure_hdr(contents) 
                procedure_body[current_proc] = (formals, [])
            elif contents == "{" and line[0] == "{":
                counts["braces"] += 1
                key = "code"
            elif contents == "}" and line[0] == "}":
                counts["braces"] += 1
                key = "global"
                current_proc = ""
            else:
                # keep incrementing current line type
                counts[key] += 1
                if key == "code":
                    (formals, body) = procedure_body[current_proc]
                    body.append(contents)
    return counts

def process_file(filename):
    print("Processing", filename)
    print("The file has", count_lines(filename), "lines.")
    print("The file has", count_non_blank_lines(filename), "non-blank lines.")
    print("The file has", count_non_comment_lines(filename), "non-comment lines.")

def process_file_lines(filename):
    counts = count_line_types(filename)
    print_counts(filename, counts)
    return counts

def print_counts(filename, counts):
    """Print the counts in the given dictionary for filename."""
    print(filename)
    sum = 0
    for k in counts:
        print(f"    {counts[k]} {k}")
        sum += counts[k]
    print(f"    {sum} TOTAL")

# loop through a folder and process all files.
def process_folder(folder, global_counts):
    """Process all files in a folder."""
    for filename in os.listdir(folder):
        if filename.endswith(".vaf"):
            counts = process_file_lines(Path(folder) / filename)
            # add counts to global counts
            for k in counts:
                global_counts[k] += counts[k]
        else:
            print("Skipping", filename)
    return global_counts

def main():
    """Main function to process a folder."""
    global_counts = defaultdict(int)
    if sys.argv[1:]:
        for folder in sys.argv[1:]:
            process_folder(folder, global_counts)
    else:
        print("Arguments: folder...")
    
    print_counts("TOTAL", global_counts)
    strip_all_asserts()
    print("DUMP OF PROCEDURES:")
    for p in procedure_body:
        if not is_evm(p + "();"):
            (formals, body) = procedure_body[p]
            code = get_flattened_code(body, formals, [f for (f,t) in formals])
            formalstr = ", ".join([f"{f}:{t}" for (f,t) in formals])
            codes = "  ".join(code)
            print(f"function {p}({formalstr}) {{ {codes} }} // {len(code)} instructions.")


if __name__ == "__main__":
    main()
