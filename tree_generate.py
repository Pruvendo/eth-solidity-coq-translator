import argparse, os, time, sys
parser = argparse.ArgumentParser(description='Generator ast and abi trees')
parser.add_argument('-i',   '--path_of_contracts')

args = parser.parse_args()
os.system("rm -rf trees")
os.system("mkdir trees")
os.system("cp -R " + args.path_of_contracts + " trees")


def list_paths_of_files(start_path:str):
    """Just get list of pair (dir, filename) """
    list_files = []
    for path, _, files in os.walk(start_path):
        for name in files:
            list_files.append((path, name))
    return list_files

def get_list_sol_files():
    """Remove non *.sol files, and return list of them"""
    list_of_files = list_paths_of_files("trees")
    for directory, file_name in list_of_files:
        if file_name[:-5] == ".json":
            os.system(f"rm {directory}/{file_name}")
    return [file for file in list_of_files if file[1][-4:] == ".sol"] 


start = time.time()
for directory, file_name in get_list_sol_files():
    generate_abi = f"solc --abi {directory}/{file_name} -o {directory}/{file_name}_folder --pretty-json"
    generate_ast = f"solc --ast-compact-json {directory}/{file_name} -o {directory}/{file_name}_folder --pretty-json"
    rename_abi = f"mv {directory}/{file_name}_folder/*.abi {directory}/{file_name}_folder/{file_name}_json.abi"
    result_abi = os.system(generate_abi)
    result_mv_abi = os.system(rename_abi)
    result_ast = os.system(generate_ast)
    
    if result_ast != 0:
        # mean with error running
        raise Exception(f"Error: Can't get ast from file: {directory}/{file_name}")
    if result_abi != 0:
        # mean with error running
        raise Exception(f"Error: Can't get abi from file: {directory}/{file_name}")


end = time.time()
print("\n", f"{end - start:.2f} s")
