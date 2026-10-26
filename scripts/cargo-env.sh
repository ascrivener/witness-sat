# Source this to let Cargo fetch the private witness git dependency as ascrivener.
export GH_TOKEN=$(gh auth token --user ascrivener) CARGO_NET_GIT_FETCH_WITH_CLI=true GIT_CONFIG_COUNT=2 \
	GIT_CONFIG_KEY_0=credential.helper GIT_CONFIG_VALUE_0= GIT_CONFIG_KEY_1=credential.helper \
	GIT_CONFIG_VALUE_1='!gh auth git-credential'
