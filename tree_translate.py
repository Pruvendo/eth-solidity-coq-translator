import argparse, os, time

parser = argparse.ArgumentParser(description='Translator eth solidity to Ursus')
parser.add_argument('-i',   '--path_of_trees')

args = parser.parse_args()
os.system("rm -rf translated")
os.system("mkdir translated")
if os.path.isfile("full.ast"):
    os.system("rm full.ast")

path_of_trees = os.path.dirname(__file__)+"/"+"trees" if args.path_of_trees == None else args.path_of_trees
print(path_of_trees)



def list_paths_of_files(start_path: str) -> list[str, str]:
    list_files = []
    for path, _, files in os.walk(start_path):
        for name in files:
            list_files.append((path, name))
    return list_files

list_files = list_paths_of_files(path_of_trees)
list_files = [(dir, file_name)for dir, file_name in list_files if file_name[:-4]!= ".sol"]


start = time.time()
# commands = "ulimit -s 64000"
commands = "echo start"
for dir, file_name in list_files:
    if dir[-11:] == ".sol_folder":
        actual_dir_name = os.path.dirname(dir)
        ast = f"{dir[:-11].removeprefix(actual_dir_name)}.sol_json.ast"
        abi = f"{dir[:-11].removeprefix(actual_dir_name)}.sol_json.abi"
        ast_name = f"{dir}/{ast}".replace("//", "/")
        abi_name = f"{dir}/{abi}".replace("//", "/")
        print(ast)
        if not (os.path.exists(ast_name) or os.path.exists(abi_name)):
            print(ast_name)
            print(abi_name)
            raise Exception("AST or ABI doesn't exist")
        command = f"_build/default/main.native {ast_name} {abi_name} {path_of_trees}"
        command = command.replace("//", "/")
        print(command)
        commands += "&&" + command
os.system(commands)
end = time.time()
print("\n", f"{end - start:.2f} s")
