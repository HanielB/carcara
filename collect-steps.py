import os
import glob

import csv, codecs, unidecode
from collections import OrderedDict

logics = ["AUFLIA","QF_AUFLIA","QF_LIA","QF_RDL","QF_UFIDL","QF_UFLRA","UF","UFLIA",
"AUFLIRA","QF_ALIA","QF_IDL","QF_LRA","QF_UF","QF_UFLIA","UFIDL","UFLRA"]

def read_files_in_subdirectories(directory, filename_pattern):
    # Create the search pattern with the provided directory and filename pattern
    search_pattern = os.path.join(directory, '**', filename_pattern)

    # Use glob to find all files that match the pattern
    files = glob.glob(search_pattern, recursive=True)

    # Read and print the content of each file
    allstats = open("steps.csv", "w")
    allstats.write("rule,count,total,mean,lower_whisker,first_quartile,median,third_quartile,upper_whisker\n")
    for f in files:
        with open(f,"rb") as stats:
            print("Read ", f)
            stats = list(csv.reader(codecs.iterdecode(stats, 'utf-8'), delimiter = ','))
            # timeout/memout or invalid
            if not stats or len(stats) == 1:
                continue
            stats = stats[1:]
            for row in stats:
              allstats.write(",".join(row) + "\n")

# Example usage
directory = 'journal-20240527-1802-bench'  # Replace with the path to your directory
filename_pattern = 'steps.csv'  # Replace with the name of the files you want to read

read_files_in_subdirectories(directory, filename_pattern)
