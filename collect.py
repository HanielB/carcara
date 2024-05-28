import os
import glob

import math, re, argparse, csv, codecs, statistics, unidecode

logics = ["AUFLIA","QF_AUFLIA","QF_LIA","QF_RDL","QF_UFIDL","QF_UFLRA","UF","UFLIA",
"AUFLIRA","QF_ALIA","QF_IDL","QF_LRA","QF_UF","QF_UFLIA","UFIDL","UFLRA"]

def read_files_in_subdirectories(directory, filename_pattern):
    # Create the search pattern with the provided directory and filename pattern
    search_pattern = os.path.join(directory, '**', filename_pattern)

    # Use glob to find all files that match the pattern
    files = glob.glob(search_pattern, recursive=True)

    # Read and print the content of each file
    allstats = open("runs.csv", "w")
    allstats.write("proof_file,run_id,parsing,checking,elaboration,total_accounted_for,total,polyeq,polyeq_ratio,assume,assume_ratio\n")
    for f in files:
        with open(f,"rb") as stats:
            print("Read ", f)
            stats = list(csv.reader(codecs.iterdecode(stats, 'utf-8'), delimiter = ','))
            # timeout/memout or invalid
            if not stats or len(stats) == 1:
                continue
            stats = stats[1:][0]
            fileName = f.split("/")[:-1]
            logicPos = next(i for i, x in enumerate(fileName) if x in logics)
            stats[0] = "/".join(fileName[logicPos:])
            allstats.write(",".join(stats)+ "\n")

# Example usage
directory = 'check'  # Replace with the path to your directory
filename_pattern = 'runs.csv'  # Replace with the name of the files you want to read

read_files_in_subdirectories(directory, filename_pattern)
