
DAEMON="simd"
HOMEDIR="$HOME/.simapp"
KEY="validator"
CHAINID="4040"
MONIKER="localtestnet"
KEYRING="test"
LOGLEVEL="info"
# to trace
#TRACE="--trace"
TRACE=""

# validate dependencies are installed
command -v jq > /dev/null 2>&1 || { echo >&2 "jq not installed. More info: https://stedolan.github.io/jq/download/"; exit 1; }

# remove existing daemon
rm -rf ~/.gaiad*

#make install

${DAEMON} config keyring-backend $KEYRING
${DAEMON} config chain-id $CHAINID

# if $KEY exists it should be deleted
#${DAEMON} keys add $KEY --algo $KEYALGO

# Set moniker and chain-id (Moniker can be anything, chain-id must be an integer)
${DAEMON} init $MONIKER --chain-id $CHAINID 

# Change parameter token denominations to stake
cat $HOMEDIR/config/genesis.json | jq '.app_state["staking"]["params"]["bond_denom"]="stake"' > $HOMEDIR/config/tmp_genesis.json && mv $HOMEDIR/config/tmp_genesis.json $HOMEDIR/config/genesis.json
cat $HOMEDIR/config/genesis.json | jq '.app_state["crisis"]["constant_fee"]["denom"]="stake"' > $HOMEDIR/config/tmp_genesis.json && mv $HOMEDIR/config/tmp_genesis.json $HOMEDIR/config/genesis.json
cat $HOMEDIR/config/genesis.json | jq '.app_state["gov"]["deposit_params"]["min_deposit"][0]["denom"]="stake"' > $HOMEDIR/config/tmp_genesis.json && mv $HOMEDIR/config/tmp_genesis.json $HOMEDIR/config/genesis.json
cat $HOMEDIR/config/genesis.json | jq '.app_state["mint"]["params"]["mint_denom"]="stake"' > $HOMEDIR/config/tmp_genesis.json && mv $HOMEDIR/config/tmp_genesis.json $HOMEDIR/config/genesis.json

# Informal audit: make deposit and voting periods small
cat $HOMEDIR/config/genesis.json | jq '.app_state["gov"]["deposit_params"]["max_deposit_period"]="5s"' > $HOMEDIR/config/tmp_genesis.json && mv $HOMEDIR/config/tmp_genesis.json $HOMEDIR/config/genesis.json
cat $HOMEDIR/config/genesis.json | jq '.app_state["gov"]["voting_params"]["voting_period"]="5s"' > $HOMEDIR/config/tmp_genesis.json && mv $HOMEDIR/config/tmp_genesis.json $HOMEDIR/config/genesis.json
cat $HOMEDIR/config/genesis.json | jq '.app_state["intrarelayer"]["params"]["token_pair_voting_period"]="120s"' > $HOMEDIR/config/tmp_genesis.json && mv $HOMEDIR/config/tmp_genesis.json $HOMEDIR/config/genesis.json
# End of Informal audit

# increase block time (?)
cat $HOMEDIR/config/genesis.json | jq '.consensus_params["block"]["time_iota_ms"]="30000"' > $HOMEDIR/config/tmp_genesis.json && mv $HOMEDIR/config/tmp_genesis.json $HOMEDIR/config/genesis.json

# Set gas limit in genesis
cat $HOMEDIR/config/genesis.json | jq '.consensus_params["block"]["max_gas"]="10000000"' > $HOMEDIR/config/tmp_genesis.json && mv $HOMEDIR/config/tmp_genesis.json $HOMEDIR/config/genesis.json

if false; then
    # disable produce empty block
    if [[ "$OSTYPE" == "darwin"* ]]; then
        sed -i '' 's/create_empty_blocks = true/create_empty_blocks = false/g' $HOMEDIR/config/config.toml
      else
        sed -i 's/create_empty_blocks = true/create_empty_blocks = false/g' $HOMEDIR/config/config.toml
    fi

    sed -i 's/create_empty_blocks_interval = "0s"/create_empty_blocks_interval = "30s"/g' $HOMEDIR/config/config.toml
    sed -i 's/timeout_propose = "3s"/timeout_propose = "30s"/g' $HOMEDIR/config/config.toml
    sed -i 's/timeout_propose_delta = "500ms"/timeout_propose_delta = "5s"/g' $HOMEDIR/config/config.toml
    sed -i 's/timeout_prevote = "1s"/timeout_prevote = "10s"/g' $HOMEDIR/config/config.toml
    sed -i 's/timeout_prevote_delta = "500ms"/timeout_prevote_delta = "5s"/g' $HOMEDIR/config/config.toml
    sed -i 's/timeout_precommit = "1s"/timeout_precommit = "10s"/g' $HOMEDIR/config/config.toml
    sed -i 's/timeout_precommit_delta = "500ms"/timeout_precommit_delta = "5s"/g' $HOMEDIR/config/config.toml
    sed -i 's/timeout_commit = "5s"/timeout_commit = "150s"/g' $HOMEDIR/config/config.toml
    sed -i 's/timeout_broadcast_tx_commit = "10s"/timeout_broadcast_tx_commit = "150s"/g' $HOMEDIR/config/config.toml

fi    

# informal      
perl -0777 -pi -e 's/# Enable defines if the API server should be enabled.\nenable = false/# Enable defines if the API server should be enabled.\nenable = true/igs' \
  $HOMEDIR/config/app.toml
sed -i 's/swagger = false/swagger = true/g' $HOMEDIR/config/app.toml

# Allocate genesis accounts (cosmos formatted addresses)
#${DAEMON} add-genesis-account $KEY 100000000000000000000000000stake

# user1: cosmos19ftpcggezgal5ascglq5m022z4e453khqatpml
# user2: cosmos1evyv7neax9qtxxzuexnhylxyz4guvsyjmwauct
# user3: cosmos1fa4283r2r6xfumedmtp68c2j9h82jvspvfe7sh
# validator: cosmos1uquty6wqc03pqpmz0t5fzh4fd5npfpd23wgr7l

# add genesis accounts from the pre-generated mnemonics
for f in /opt/chain/mnemonics/*.txt
do
  key_name=`basename $f .txt`
  echo "Adding account $key_name from mnemonic file $f"
  ${DAEMON} keys add $key_name --recover --keyring-backend test < $f  
  ${DAEMON} add-genesis-account $key_name \
      1000000000000000000000000000stake
done

# Sign genesis transaction
${DAEMON} gentx $KEY 1000000000000000000000stake --chain-id $CHAINID

# Collect genesis tx
${DAEMON} collect-gentxs

# Run this to ensure everything worked and that the genesis file is setup correctly
${DAEMON} validate-genesis

# Start the node (remove the --pruning=nothing flag if historical queries are not needed)
#${DAEMON} start --pruning=nothing $TRACE --log_level $LOGLEVEL --minimum-gas-prices=0.0001stake --json-rpc.api eth,txpool,personal,net,debug,web3
