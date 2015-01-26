> results.out
for file in *.smt2
do
  echo $file
  echo >> results.out
  echo $file >> results.out
  echo  >> results.out
  python ddsmt.py $file output.smt2 echo >> results.out
done

echo >> results.out
SUC=`grep -c "[Rr]efuted" results.out`
FAIL=`grep -c "[Ff]ailed" results.out`
echo "Polya has succeeded on: " >> results.out
echo $SUC >> results.out
echo "and failed on: " >> results.out
echo $FAIL >> results.out