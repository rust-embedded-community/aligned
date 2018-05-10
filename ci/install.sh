set -euxo pipefail

main() {
    if [ $TARGET != x86_64-unknonwn-linux-gnu ]; then
        rustup target add $TARGET
    fi
}

main
