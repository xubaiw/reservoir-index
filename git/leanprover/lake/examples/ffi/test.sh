set -e

./clean.sh
./package.sh
./app/build/bin/app
./lib/build/bin/test

${LAKE:-../../build/bin/lake} -d app build Test
