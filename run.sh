for file in *.smt2
do
  echo $file
  python ddsmt.py $file output.smt2 echo >> results.out
done