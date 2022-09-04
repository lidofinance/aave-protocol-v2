if [[ "$1" ]]
then
    RULE="--rule $1"
fi

certoraRun contracts/protocol/tokenization/lido/AStETH.sol certora/harness/IncentivesControllerMock.sol certora/harness/SymbolicLendingPool.sol certora/harness/DummyERC20A.sol certora/harness/DummyERC20B.sol \
           --verify AStETH:certora/specs/AStETH.spec \
           --link AStETH:UNDERLYING_ASSET_ADDRESS=DummyERC20A AStETH:POOL=SymbolicLendingPool AStETH:_incentivesController=IncentivesControllerMock AStETH:RESERVE_TREASURY_ADDRESS=DummyERC20B SymbolicLendingPool:aToken=AStETH SymbolicLendingPool:Asset=DummyERC20A \
           --solc solc6.12 \
           --optimistic_loop \
           --settings -smt_nonLinearArithmetic=true \
           --staging \
           $RULE \
           --msg "AStETH $RULE $2"
