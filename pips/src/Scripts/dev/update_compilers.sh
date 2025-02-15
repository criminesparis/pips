#! /bin/bash
#
# $Id: update_compilers.sh 23658 2022-05-22 09:43:09Z coelho $
#
# update compiled compilers for GCC8X GCC9X GCCTK CLGTK
#
# GCC5X: last update oct 2017
# GCC6X: last update nov 2018
# GCC7X: last update nov 2019
# GCC8X: maintained
# GCC9X: maintained
# GCC10: maintained

# git clone git://gcc.gnu.org/git/gcc.git gcc-src # 1.7G
# git branch gcc-trunk origin/master
# git branch gcc-X origin/releases/gcc-X
#
# FIXME exit on first error, should it go on?

gcc_src=$HOME/gcc-src
build=$HOME/build
out=/tmp/update_compiler

# GCC branches
pushd $gcc_src
git clean -xdf || exit 1

for ver in trunk 10 9 8 ; do
  gcc=gcc-$ver
  echo "# compiling $gcc"

  (
    git checkout $gcc || exit 2
    git pull || exit 3
    # generate version information
    rev=$(git log -1|head -1|perl -p -e 's/^commit ([a-f0-9]{8})[a-f0-9]*/$1/')
    date=$(git log -1 --date=iso8601 | sed -n 3p | cut -c 9-18 | tr -d '-')
    # build
    test -d $build && rm -rf $build
    mkdir $build || exit 4
    pushd $build
    $gcc_src/configure --prefix=$HOME/$gcc-bin &&
      make -j 32 bootstrap &&
      rm -rf $HOME/$gcc-bin.old &&
      mv $HOME/$gcc-bin $HOME/$gcc-bin.old &&
      make -j1 install ||
        { echo "error building $gcc" >&2 ; exit 6 ; }
    pushd $HOME/$gcc-bin/bin && ln -s ./gcc cc && popd
    popd # $build
    rm -rf $build
    git clean -xdf || exit 5
    echo "# done $gcc $date $rev"
    echo -n "$ver $date $rev" > $HOME/$gcc-bin/version
  ) > $out.$ver 2>&1
  echo "# $gcc done $?"
done

popd # $gcc_src

# CLANG
# git clone https://github.com/llvm/llvm-project.git $HOME/llvm-src # 1.9G

llvm_src=$HOME/llvm-src
pushd $llvm_src

git clean -xdf || exit 1
git pull || exit 2
# keep version info... should exit on error above?
rev=$(git log -1 | head -1 | perl -p -e 's/^commit ([a-f0-9]{8})[a-f0-9]*/$1/')
date=$(git log -1 --date=iso8601 | sed -n 3p | cut -c 9-18 | tr -d '-')

echo '# compiling clang'
(
  test -d $build && rm -rf $build
  mkdir $build || exit 3
  pushd $build
  # FIXME can it compile with clang?
  # PATH=$HOME/clgtk/bin:$PATH
  PATH=$HOME/gcc-10-bin/bin:$PATH
  cmake -G "Unix Makefiles" \
    -DLLVM_ENABLE_PROJECTS="clang" \
    -DLLVM_ENABLE_RUNTIMES="libcxx;libcxxabi" \
    -DLLVM_TARGETS_TO_BUILD="X86" \
    -DLLVM_PARALLEL_LINK_JOBS=4 \
    -DBUILD_SHARED_LIBS=true \
    -DCMAKE_INSTALL_PREFIX=$HOME/clgtk \
    -DCMAKE_BUILD_TYPE=Debug \
    $llvm_src/llvm &&
    make -j 16 &&
    rm -rf $HOME/clgtk.old &&
    mv $HOME/clgtk $HOME/clgtk.old &&
    make install ||
      { echo "error building clang" >&2 ; exit 6 ; }
  popd # $build
  rm -rf $build
  git clean -xdf || exit 5
  echo "# done llvm-trunk $date $rev"
  echo -n "main $date $rev" > $HOME/clgtk/version
  # we need a working "cc"
  ln -s ./clang $HOME/clgtk/bin/cc
) > $out.clang 2>&1

echo "# clang done $?"

# final cleanup
git clean -xdf || exit 1
popd # $llvm_src

echo '# done'
