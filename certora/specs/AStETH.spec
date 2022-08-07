import "./AStETH_summerizations.spec"

using SymbolicLendingPool as LENDING_POOL
using DummyERC20A as UNDERLYING_ASSET
using DummyERC20B as RESERVE_TREASURY

methods {    

    getRevision() returns (uint256)
    initialize(uint8, string, string) envfree
    initializing() envfree
    balanceOf(address) returns (uint256) envfree
    scaledBalanceOf(address) returns (uint256) envfree
    internalBalanceOf(address) returns (uint256) envfree
    getScaledUserBalanceAndSupply(address) returns (uint256, uint256) envfree
    totalSupply() returns (uint256) envfree
    scaledTotalSupply() returns (uint256) envfree
    internalTotalSupply() returns (uint256) envfree
    burn(address, address,uint256, uint256)
    mint(address, uint256, uint256)
    mintToTreasury(uint256, uint256)
    transferOnLiquidation(address, address, uint256) 
    transferUnderlyingTo(address, uint256) returns (uint256) 
    permit(address, address, uint256, uint256, uint8, bytes32, bytes32) 

    isContractIsTrue(address) returns (bool) envfree

    UNDERLYING_ASSET.balanceOf(address) returns (uint256) envfree
    UNDERLYING_ASSET.totalSupply() returns (uint256) envfree

    LENDING_POOL.aToken() returns (address) envfree

    RESERVE_TREASURY_ADDRESS() returns (address) envfree

}

/*
    @Rule

    @Description:
        The balance of a reciver in TransferUnderlyingTo() should increase by amount
        The balance of a sender in TransferUnderlyingTo() should decrease by amount

    @Formula:
        {
            user != currentContract;
        }

        transferUnderlyingTo(user, amount)
        
        {
            userBalanceAfter == userBalanceBefore + amountTransfered;
            totalSupplyAfter == totalSupplyBefore - amountTransfered;
        }

    @Note:

    @Link:
*/

rule integrityOfTransferUnderlyingTo(address user, uint256 amount) {
    env e;
    require user != currentContract;

    mathint totalSupplyBefore = UNDERLYING_ASSET.balanceOf(currentContract);
    mathint userBalanceBefore = UNDERLYING_ASSET.balanceOf(user);

    uint256 amountTransfered = transferUnderlyingTo(e, user, amount);

    mathint totalSupplyAfter = UNDERLYING_ASSET.balanceOf(currentContract);
    mathint userBalanceAfter = UNDERLYING_ASSET.balanceOf(user);

    assert userBalanceAfter == userBalanceBefore + amountTransfered;
    assert totalSupplyAfter == totalSupplyBefore - amountTransfered;
}

/*
    @Rule

    @Description:
        Minting AStETH must increase the AStETH totalSupply and user's balance

    @Formula:
        {

        }

        mint()
        
        {
            _ATokenInternalBalance < ATokenInternalBalance_ &&
            _ATokenScaledBalance < ATokenScaledBalance_ &&
            _ATokenBalance < ATokenBalance_ &&
            _ATokenInternalTotalSupply < ATokenInternalTotalSupply_ &&
            _ATokenScaledTotalSupply < ATokenScaledTotalSupply_ &&
            _ATokenTotalSupply < ATokenTotalSupply_
        }

    @Note:

    @Link:
*/

rule monotonicityOfMint(address user, uint256 amount, uint256 index) {
	env e;

    mathint _ATokenInternalBalance = internalBalanceOf(user);
    mathint _ATokenScaledBalance = scaledBalanceOf(user);
    mathint _ATokenBalance = balanceOf(user);
    mathint _ATokenInternalTotalSupply = internalTotalSupply();
    mathint _ATokenScaledTotalSupply = scaledTotalSupply();
    mathint _ATokenTotalSupply = totalSupply();
    
    mint(e, user, amount, index);
    
    mathint ATokenInternalBalance_ = internalBalanceOf(user);
    mathint ATokenScaledBalance_ = scaledBalanceOf(user);
    mathint ATokenBalance_ = balanceOf(user);
    mathint ATokenInternalTotalSupply_ = internalTotalSupply();
    mathint ATokenScaledTotalSupply_ = scaledTotalSupply();
    mathint ATokenTotalSupply_ = totalSupply();
    
    assert _ATokenInternalBalance < ATokenInternalBalance_;
    assert _ATokenScaledBalance < ATokenScaledBalance_;
    assert _ATokenBalance < ATokenBalance_;
    assert _ATokenInternalTotalSupply < ATokenInternalTotalSupply_;
    assert _ATokenScaledTotalSupply < ATokenScaledTotalSupply_;
    assert _ATokenTotalSupply < ATokenTotalSupply_;
}

/*
    @Rule

    @Description:
        Burning AStETH must decrease the AStETH totalSupply and user's balance.
        It should also not decrease reciver's underlying asset.

    @Formula:
        {

        }

        burn()
        
        {
            _ATokenInternalBalance > ATokenInternalBalance_ &&
            _ATokenScaledBalance > ATokenScaledBalance_ &&
            _ATokenBalance > ATokenBalance_ &&
            _ATokenInternalTotalSupply > ATokenInternalTotalSupply_ &&
            _ATokenScaledTotalSupply > ATokenScaledTotalSupply_ &&
            _ATokenTotalSupply > ATokenTotalSupply_ &&
            _underlyingReciverBalance <= underlyingReciverBalance_ &&
            _underlyingTotalSupply == underlyingTotalSupply_
        }

    @Note:

    @Link:
*/

rule monotonicityOfBurn(address user, address reciver, uint256 amount, uint256 index) {
	env e;

    mathint _ATokenInternalBalance = internalBalanceOf(user);
    mathint _ATokenScaledBalance = scaledBalanceOf(user);
    mathint _ATokenBalance = balanceOf(user);
    mathint _ATokenInternalTotalSupply = internalTotalSupply();
    mathint _ATokenScaledTotalSupply = scaledTotalSupply();
    mathint _ATokenTotalSupply = totalSupply();
    mathint _underlyingReciverBalance = UNDERLYING_ASSET.balanceOf(reciver);
    
    burn(e, user, reciver, amount, index);
    
    mathint ATokenInternalBalance_ = internalBalanceOf(user);
    mathint ATokenScaledBalance_ = scaledBalanceOf(user);
    mathint ATokenBalance_ = balanceOf(user);
    mathint ATokenInternalTotalSupply_ = internalTotalSupply();
    mathint ATokenScaledTotalSupply_ = scaledTotalSupply();
    mathint ATokenTotalSupply_ = totalSupply();
    mathint underlyingReciverBalance_ = UNDERLYING_ASSET.balanceOf(reciver);
    
    
    assert _ATokenInternalBalance > ATokenInternalBalance_;
    assert _ATokenScaledBalance > ATokenScaledBalance_;
    assert _ATokenBalance > ATokenBalance_;
    assert _ATokenInternalTotalSupply > ATokenInternalTotalSupply_;
    assert _ATokenScaledTotalSupply > ATokenScaledTotalSupply_;
    assert _ATokenTotalSupply > ATokenTotalSupply_;
    
    assert _underlyingReciverBalance <= underlyingReciverBalance_;
}

/*
    @Rule

    @Description:
        Minting and burning are invert operations within the AStETH context

    @Formula:
        {

        }

        mint()
        burn()
        
        {
            _ATokenInternalBalance == ATokenInternalBalance_ &&
            _ATokenScaledBalance == ATokenScaledBalance_ &&
            _ATokenBalance == ATokenBalance_ &&
            _ATokenInternalTotalSupply == ATokenInternalTotalSupply_ &&
            _ATokenScaledTotalSupply == ATokenScaledTotalSupply_ &&
            _ATokenTotalSupply == ATokenTotalSupply_
        }

    @Note:

    @Link:
*/

rule mintBurnInvertability(address user, uint256 amount, uint256 index, address reciver){
    env e;
    
    mathint _ATokenInternalBalance = internalBalanceOf(user);
    mathint _ATokenScaledBalance = scaledBalanceOf(user);
    mathint _ATokenBalance = balanceOf(user);
    mathint _ATokenInternalTotalSupply = internalTotalSupply();
    mathint _ATokenScaledTotalSupply = scaledTotalSupply();
    mathint _ATokenTotalSupply = totalSupply();
    
    mint(e, user, amount, index);
    burn(e, user, reciver, amount, index);
    
    mathint ATokenInternalBalance_ = internalBalanceOf(user);
    mathint ATokenScaledBalance_ = scaledBalanceOf(user);
    mathint ATokenBalance_ = balanceOf(user);
    mathint ATokenInternalTotalSupply_ = internalTotalSupply();
    mathint ATokenScaledTotalSupply_ = scaledTotalSupply();
    mathint ATokenTotalSupply_ = totalSupply();
    
    assert _ATokenInternalBalance == ATokenInternalBalance_;
    assert _ATokenScaledBalance == ATokenScaledBalance_;
    assert _ATokenBalance == ATokenBalance_;
    assert _ATokenInternalTotalSupply == ATokenInternalTotalSupply_;
    assert _ATokenScaledTotalSupply == ATokenScaledTotalSupply_;
    assert _ATokenTotalSupply == ATokenTotalSupply_;
}

/*
    @Rule

    @Description:
        AStETH cannot change the totalSupply of the underlying asset

    @Formula:
        {

        }

        < call any function >
        
        {
            _underlyingTotalSupply == underlyingTotalSupply_
        }

    @Note:

    @Link:
*/

rule aTokenCantAffectUnderlying(){
    env e; calldataarg args; method f;

    mathint _underlyingTotalSupply = UNDERLYING_ASSET.totalSupply();
    f(e, args);
    mathint underlyingTotalSupply_ = UNDERLYING_ASSET.totalSupply();

    assert _underlyingTotalSupply == underlyingTotalSupply_;
}

/*
    @Rule

    @Description:
        Check that each possible operation changes the balance of at most two users

    @Formula:
        {

        }

        < call any function >
        
        {
            _ATokenInternalBalance1 == ATokenInternalBalance1_ || _ATokenInternalBalance2 == ATokenInternalBalance2_ || _ATokenInternalBalance3 == ATokenInternalBalance3_
            _ATokenScaledBalance1 == ATokenScaledBalance1_ || _ATokenScaledBalance2 == ATokenScaledBalance2_ || _ATokenScaledBalance3 == ATokenScaledBalance3_
            _ATokenBalance1 == ATokenBalance1_ || _ATokenBalance2 == ATokenBalance2_ || _ATokenBalance3 == ATokenBalance3_
        }

    @Note:

    @Link:
*/

rule operationAffectMaxTwo(address user1, address user2, address user3)
{
	env e; calldataarg arg; method f;
	require user1!=user2 && user1!=user3 && user2!=user3;
    mathint _ATokenInternalBalance1 = internalBalanceOf(user1);
    mathint _ATokenInternalBalance2 = internalBalanceOf(user2);
    mathint _ATokenInternalBalance3 = internalBalanceOf(user3);
    mathint _ATokenScaledBalance1 = scaledBalanceOf(user1);
    mathint _ATokenScaledBalance2 = scaledBalanceOf(user2);
    mathint _ATokenScaledBalance3 = scaledBalanceOf(user3);
    mathint _ATokenBalance1 = balanceOf(user1);
    mathint _ATokenBalance2 = balanceOf(user2);
    mathint _ATokenBalance3 = balanceOf(user3);
	
    f(e, arg);

    mathint ATokenInternalBalance1_ = internalBalanceOf(user1);
    mathint ATokenInternalBalance2_ = internalBalanceOf(user2);
    mathint ATokenInternalBalance3_ = internalBalanceOf(user3);
    mathint ATokenScaledBalance1_ = scaledBalanceOf(user1);
    mathint ATokenScaledBalance2_ = scaledBalanceOf(user2);
    mathint ATokenScaledBalance3_ = scaledBalanceOf(user3);
    mathint ATokenBalance1_ = balanceOf(user1);
    mathint ATokenBalance2_ = balanceOf(user2);
    mathint ATokenBalance3_ = balanceOf(user3);

	assert (_ATokenInternalBalance1 == ATokenInternalBalance1_ || _ATokenInternalBalance2 == ATokenInternalBalance2_ || _ATokenInternalBalance3 == ATokenInternalBalance3_);
	assert (_ATokenScaledBalance1 == ATokenScaledBalance1_ || _ATokenScaledBalance2 == ATokenScaledBalance2_ || _ATokenScaledBalance3 == ATokenScaledBalance3_);
	assert (_ATokenBalance1 == ATokenBalance1_ || _ATokenBalance2 == ATokenBalance2_ || _ATokenBalance3 == ATokenBalance3_);

}

/*
    @Rule

    @Description:
        Check that the changes to total supply are coherent with the changes to balance

    @Formula:
        {

        }

        < call any function >
        
        {
            ((ATokenInternalBalance1_ != _ATokenInternalBalance1) && (ATokenInternalBalance2_ != _ATokenInternalBalance2)) =>
            (ATokenInternalBalance1_ - _ATokenInternalBalance1) + (ATokenInternalBalance2_ - _ATokenInternalBalance2)  == (ATokenInternalTotalSupply_ - _ATokenInternalTotalSupply);
            
            ((ATokenScaledBalance1_ != _ATokenScaledBalance1) && (ATokenScaledBalance2_ != _ATokenScaledBalance2)) =>
            (ATokenScaledBalance1_ - _ATokenScaledBalance1) + (ATokenScaledBalance2_ - _ATokenScaledBalance2)  == (ATokenScaledTotalSupply_ - _ATokenScaledTotalSupply);
            
            ((ATokenBalance1_ != _ATokenBalance1) && (ATokenBalance2_ != _ATokenBalance2)) =>
            (ATokenBalance1_ - _ATokenBalance1) + (ATokenBalance2_ - _ATokenBalance2)  == (ATokenTotalSupply_ - ATokenTotalSupply_);
        }

    @Note:

    @Link:
*/

rule integrityBalanceOfTotalSupply(address user1, address user2){
	env e; calldataarg arg; method f;
    require user1 != user2;
	
    mathint _ATokenInternalBalance1 = internalBalanceOf(user1);
    mathint _ATokenInternalBalance2 = internalBalanceOf(user2);
    mathint _ATokenScaledBalance1 = scaledBalanceOf(user1);
    mathint _ATokenScaledBalance2 = scaledBalanceOf(user2);
    mathint _ATokenBalance1 = balanceOf(user1);
    mathint _ATokenBalance2 = balanceOf(user2);
    mathint _ATokenInternalTotalSupply = internalTotalSupply();
    mathint _ATokenScaledTotalSupply = scaledTotalSupply();
    mathint _ATokenTotalSupply = totalSupply();
	 
	f(e, arg); 

    mathint ATokenInternalBalance1_ = internalBalanceOf(user1);
    mathint ATokenInternalBalance2_ = internalBalanceOf(user2);
    mathint ATokenScaledBalance1_ = scaledBalanceOf(user1);
    mathint ATokenScaledBalance2_ = scaledBalanceOf(user2);
    mathint ATokenBalance1_ = balanceOf(user1);
    mathint ATokenBalance2_ = balanceOf(user2);
    mathint ATokenInternalTotalSupply_ = internalTotalSupply();
    mathint ATokenScaledTotalSupply_ = scaledTotalSupply();
    mathint ATokenTotalSupply_ = totalSupply();

    assert ((ATokenInternalBalance1_ != _ATokenInternalBalance1) && (ATokenInternalBalance2_ != _ATokenInternalBalance2)) =>
            (ATokenInternalBalance1_ - _ATokenInternalBalance1) + (ATokenInternalBalance2_ - _ATokenInternalBalance2)  == (ATokenInternalTotalSupply_ - _ATokenInternalTotalSupply);
    assert ((ATokenScaledBalance1_ != _ATokenScaledBalance1) && (ATokenScaledBalance2_ != _ATokenScaledBalance2)) =>
            (ATokenScaledBalance1_ - _ATokenScaledBalance1) + (ATokenScaledBalance2_ - _ATokenScaledBalance2)  == (ATokenScaledTotalSupply_ - _ATokenScaledTotalSupply);
    assert ((ATokenBalance1_ != _ATokenBalance1) && (ATokenBalance2_ != _ATokenBalance2)) =>
            (ATokenBalance1_ - _ATokenBalance1) + (ATokenBalance2_ - _ATokenBalance2)  == (ATokenTotalSupply_ - ATokenTotalSupply_);
}

/*
    @Rule

    @Description:
        Checks that the totalSupply of AStETH must be backed by underlying asset in the contract when deposit is called (and hence mint)
        Checks that the totalSupply of AStETH must be backed by underlying asset in the contract when withdraw is called (and hence burn)

    @Formula:
        {
            _underlyingBalance >= _aTokenTotalSupply
        }

        LENDING_POOL.deposit(UNDERLYING_ASSET, amount, user, referralCode);
                                    OR
        LENDING_POOL.withdraw(e, UNDERLYING_ASSET, amount, user);

        {
            msg.sender != currentContract => underlyingBalance_ >= aTokenTotalSupply_
        }

    @Note:

    @Link:
    
*/

rule atokenPeggedToUnderlying(env e, uint256 amount, address user, uint16 referralCode){
    uint8 case;
    mathint _underlyingBalance = UNDERLYING_ASSET.balanceOf(currentContract);
    mathint _aTokenTotalSupply = internalTotalSupply();

    require _underlyingBalance >= _aTokenTotalSupply;
    require LENDING_POOL.aToken() == currentContract;
    
    if (case == 0){
        LENDING_POOL.deposit(e, UNDERLYING_ASSET, amount, user, referralCode);
    }
    else if (case == 1){
        LENDING_POOL.withdraw(e, UNDERLYING_ASSET, amount, user);
    }
    
    mathint underlyingBalance_ = UNDERLYING_ASSET.balanceOf(currentContract);
    mathint aTokenTotalSupply_ = internalTotalSupply();

    // Here the LHS of the implication is vital since a case where AStETH calls deposit will cause the backing token to be unchanged while Atokens will be minted.
    // This LHS demand is fine since AStETH cannot actively call deposit from lending pool, nor there is an `execute` method that allows calling methods externally from other contracts.
    assert e.msg.sender != currentContract => underlyingBalance_ >= aTokenTotalSupply_;
}

/*
    @Rule

    @Description:ֿ
        The AStETH totalSupply, tracked by the contract, is the sum of AStETH balances across all users.

    @Formula:
        totalsGhost() == internalTotalSupply()

    @Note:

    @Link:
    
*/

invariant totalSupplyIsSumOfBalances()
    totalsGhost() == internalTotalSupply()

/*
    @Rule

    @Description:ֿ
        The AStETH balance of a single user is less or equal to the total supply

    @Formula:
        totalsGhost() >= internalBalanceOf(user)

    @Note: 
        For every function that implements a transfer between 2 users within the system, we required that the sum of balances of the 2 users start as less than the totalSupply.
        

    @Link:
    
*/

invariant totalSupplyGESingleUserBalance(address user, env e)
    totalsGhost() >= internalBalanceOf(user)
    {
        preserved transferFrom(address spender, address reciever, uint256 amount) with (env e2) {
            require internalBalanceOf(user) + internalBalanceOf(spender) <= totalsGhost();
        }
        preserved transfer(address reciever, uint256 amount) with (env e3) {
            require e3.msg.sender == e.msg.sender;
            require internalBalanceOf(user) + internalBalanceOf(e3.msg.sender) <= totalsGhost();
        }
        preserved transferOnLiquidation(address from, address to, uint256 amount) with (env e4) {
            require internalBalanceOf(user) + internalBalanceOf(from) <= totalsGhost(); 
        }
        preserved burn(address owner, address recieverUnderlying, uint256 amount, uint256 index)  with (env e5) {
            require internalBalanceOf(user) + internalBalanceOf(owner) <= totalsGhost(); 
        }
    }

/*
    @Rule

    @Description:ֿ
        burn operation is additive

    @Formula:

        burn(user, receiverOfUnderlying, amount1, index) at initialStorage;
        burn(user, receiverOfUnderlying, amount2, index) at initialStorage;

        {
            balanceOfUnderlyingTokenAfterSeparate := UNDERLYING_ASSET.balanceOf(receiverOfUnderlying);
            balanceSeparate := balanceOf(user);
            totalSupplySeparate := totalSupply();
        }
        
        ~

        burn(user, receiverOfUnderlying, amount1 + amount2, index) at initialStorage;

        {
            balanceOfUnderlyingTokenAfterSeparate == UNDERLYING_ASSET.balanceOf(receiverOfUnderlying);
            balanceSeparate == balanceOf(user);
            totalSupplySeparate == totalSupply();
        }

    @Note:        

    @Link:
    
*/

rule burnAdditive(
    address user,
    address receiverOfUnderlying,
    uint256 amount1,
    uint256 amount2,
    uint256 index
) {
    env e;
    storage initialStorage = lastStorage;
    burn(e, user, receiverOfUnderlying, amount1, index);
    burn(e, user, receiverOfUnderlying, amount2, index);
    mathint balanceOfUnderlyingTokenAfterSeparate = UNDERLYING_ASSET.balanceOf(receiverOfUnderlying);
    uint256 balanceSeparate = balanceOf(user);
    mathint totalSupplySeparate = totalSupply();
    burn(e, user, receiverOfUnderlying, amount1 + amount2, index) at initialStorage;
    mathint balanceOfUnderlyingTokenAfterCombined = UNDERLYING_ASSET.balanceOf(receiverOfUnderlying);
    uint256 balanceCombined = balanceOf(user);
    mathint totalSupplyCombined = totalSupply();
    assert balanceOfUnderlyingTokenAfterSeparate == balanceOfUnderlyingTokenAfterCombined;
    assert balanceSeparate == balanceCombined;
    assert totalSupplySeparate == totalSupplyCombined;
}

/*
    @Rule

    @Description:ֿ
        mint operation is additive

    @Formula:

        mint(user, amount1, index);
        mint(user, amount2, index);

        {
            balanceOfUnderlyingTokenAfterSeparate := UNDERLYING_ASSET.balanceOf(receiverOfUnderlying),
            balanceSeparate := balanceOf(user),
            totalSupplySeparate := totalSupply()
        }
        
        ~
        
        mint(user, amount1 + amount2, index)

        {
            balanceOfUnderlyingTokenAfterSeparate == UNDERLYING_ASSET.balanceOf(receiverOfUnderlying),
            balanceSeparate == balanceOf(user),
            totalSupplySeparate == totalSupply()
        }

    @Note:        

    @Link:
    
*/

rule mintAdditive(
    address user,
    uint256 amount1,
    uint256 amount2,
    uint256 index
) {
    env e;
    storage initialState = lastStorage;
    mint(e, user, amount1, index);
    mint(e, user, amount2, index);
    mathint balanceOfUnderlyingTokenAfterSeparate = UNDERLYING_ASSET.balanceOf(user);
    uint256 balanceSeparate = balanceOf(user);
    mathint totalSupplySeparate = totalSupply();
    mint(e, user, amount1 + amount2, index) at initialState;
    mathint balanceOfUnderlyingTokenAfterCombined = UNDERLYING_ASSET.balanceOf(user);
    uint256 balanceCombined = balanceOf(user);
    mathint totalSupplyCombined = totalSupply();
    assert balanceOfUnderlyingTokenAfterSeparate == balanceOfUnderlyingTokenAfterCombined;
    assert balanceSeparate == balanceCombined;
    assert totalSupplySeparate == totalSupplyCombined;
}

/*
    @Rule

    @Description:ֿ
        transferUnderlyingTo operation is additive

    @Formula:

        transferUnderlyingTo(target, amount1)
        transferUnderlyingTo(target, amount2)

        {
            _balance := UNDERLYING_ASSET.balanceOf(target)
        }
        
        ~
        
        transferUnderlyingTo(target, amount1 + amount2)

        {
            _balance == UNDERLYING_ASSET.balanceOf(target)
        }

    @Note:        

    @Link:
    
*/

rule transferUnderlyingToAdditivity(address target, uint256 amount1, uint256 amount2) {
    env e;
    storage init = lastStorage;
    transferUnderlyingTo(e, target, amount1);
    transferUnderlyingTo(e, target, amount2);

    uint256 _balance = UNDERLYING_ASSET.balanceOf(target);

    transferUnderlyingTo(e, target, amount1 + amount2) at init;

    uint256 balance_ = UNDERLYING_ASSET.balanceOf(target);

    assert _balance == balance_;
}

/*
    @Rule

    @Description:ֿ
        mint operation do not affect the totalSupply or UserBalanceOfUnderlyingAsset

    @Formula:

        {
            _underlyingBalance >= _aTokenTotalSupply
        }
            LENDING_POOL.deposit(UNDERLYING_ASSET, amount, user, referralCode)
        {
            msg.sender ≠ currentContract => underlyingBalance_ >= aTokenTotalSupply_
        }

    @Note:        

    @Link:
    
*/

rule mintPreservesUnderlyingAsset(
    address user,
    uint256 amount,
    uint256 index
) {
    env e;
    mathint totalSupplyOfUnderlyingAssetBefore = UNDERLYING_ASSET.totalSupply();
    mathint balanceOfUnderlyingAssetBefore = UNDERLYING_ASSET.balanceOf(user);
    mint(e, user, amount, index);
    mathint totalSupplyOfUnderlyingAssetAfter = UNDERLYING_ASSET.totalSupply();
    mathint balanceOfUnderlyingAssetAfter = UNDERLYING_ASSET.balanceOf(user);
    assert totalSupplyOfUnderlyingAssetAfter == totalSupplyOfUnderlyingAssetBefore;
    assert balanceOfUnderlyingAssetBefore == balanceOfUnderlyingAssetAfter;
}

/*
    @Rule

    @Description:
        scaledBalance / internalBalance should be always equal to scaledTotalSupply / internalTotalSupply,
        that is, 
        internalBalance * scaledTotalSupply should be always equal to scaledBalance * internalTotalSupply,
        similarly, 
        scaledBalance * totalSupply should be always equal to balance * scaledTotalSupply, and
        internalBalance * totalSupply should be always equal to balance * internalTotalSupply

    @Formula:
        {
            _ATokenInternalBalance * _ATokenScaledTotalSupply == _ATokenScaledBalance * _ATokenInternalTotalSupply &&
            _ATokenScaledBalance * _ATokenTotalSupply == _ATokenBalance * _ATokenScaledTotalSupply &&
            _ATokenInternalBalance * _ATokenTotalSupply == _ATokenBalance * _ATokenInternalTotalSupply
        }

        < call any function >
        
        {
            ATokenInternalBalance_ * ATokenScaledTotalSupply_ == ATokenScaledBalance_ * ATokenInternalTotalSupply_ &&
            ATokenScaledBalance_ * ATokenTotalSupply_ == ATokenBalance_ * ATokenScaledTotalSupply_ &&
            ATokenInternalBalance_ * ATokenTotalSupply_ == ATokenBalance_ * ATokenInternalTotalSupply_
        }

    @Note:

    @Link:
*/

rule proportionalBalancesAndTotalSupplies(address user) {
    mathint _ATokenInternalBalance = internalBalanceOf(user);
    mathint _ATokenScaledBalance = scaledBalanceOf(user);
    mathint _ATokenBalance = balanceOf(user);
    mathint _ATokenInternalTotalSupply = internalTotalSupply();
    mathint _ATokenScaledTotalSupply = scaledTotalSupply();
    mathint _ATokenTotalSupply = totalSupply();
    require _ATokenInternalBalance * _ATokenScaledTotalSupply == _ATokenScaledBalance * _ATokenInternalTotalSupply;
    require _ATokenScaledBalance * _ATokenTotalSupply == _ATokenBalance * _ATokenScaledTotalSupply;
    require _ATokenInternalBalance * _ATokenTotalSupply == _ATokenBalance * _ATokenInternalTotalSupply;
    env e; calldataarg args; method f;
    f(e, args);
    mathint ATokenInternalBalance_ = internalBalanceOf(user);
    mathint ATokenScaledBalance_ = scaledBalanceOf(user);
    mathint ATokenBalance_ = balanceOf(user);
    mathint ATokenInternalTotalSupply_ = internalTotalSupply();
    mathint ATokenScaledTotalSupply_ = scaledTotalSupply();
    mathint ATokenTotalSupply_ = totalSupply();
    assert ATokenInternalBalance_ * ATokenScaledTotalSupply_ == ATokenScaledBalance_ * ATokenInternalTotalSupply_;
    assert ATokenScaledBalance_ * ATokenTotalSupply_ == ATokenBalance_ * ATokenScaledTotalSupply_;
    assert ATokenInternalBalance_ * ATokenTotalSupply_ == ATokenBalance_ * ATokenInternalTotalSupply_;
}

/*
    @Rule

    @Description:
        Minting to RESERVE_TREASURY_ADDRESS and invoking mintToTreasury method should be equivalent

    @Formula:

        mintToTreasury(amount, index) 

         { 
        _ATokenInternalBalance := internalBalanceOf(RESERVE_TREASURY_ADDRESS()),
        _ATokenScaledBalance := scaledBalanceOf(RESERVE_TREASURY_ADDRESS()),
        _ATokenBalance := balanceOf(RESERVE_TREASURY_ADDRESS()),
        _ATokenInternalTotalSupply := internalTotalSupply(),
        _ATokenScaledTotalSupply := scaledTotalSupply(),
        _ATokenTotalSupply := totalSupply()
        }
        ~

        mint(RESERVE_TREASURY_ADDRESS(), amount, index) at init

        {
            _ATokenInternalBalance == internalBalanceOf(RESERVE_TREASURY_ADDRESS()) &&
            _ATokenScaledBalance == scaledBalanceOf(RESERVE_TREASURY_ADDRESS()) &&
            _ATokenBalance == balanceOf(RESERVE_TREASURY_ADDRESS()) &&
            _ATokenInternalTotalSupply == internalTotalSupply() &&
            _ATokenScaledTotalSupply == scaledTotalSupply() &&
            _ATokenTotalSupply == totalSupply()
        }

    @Note:

    @Link:
*/


rule equivalenceOfMint(uint256 amount, uint256 index) {
    env e;
    storage init = lastStorage;
    mintToTreasury(e, amount, index);
    mathint _ATokenInternalBalance = internalBalanceOf(RESERVE_TREASURY_ADDRESS());
    mathint _ATokenScaledBalance = scaledBalanceOf(RESERVE_TREASURY_ADDRESS());
    mathint _ATokenBalance = balanceOf(RESERVE_TREASURY_ADDRESS());
    mathint _ATokenInternalTotalSupply = internalTotalSupply();
    mathint _ATokenScaledTotalSupply = scaledTotalSupply();
    mathint _ATokenTotalSupply = totalSupply();
    mint(e, RESERVE_TREASURY_ADDRESS(), amount, index) at init;
    mathint ATokenInternalBalance_ = internalBalanceOf(RESERVE_TREASURY_ADDRESS());
    mathint ATokenScaledBalance_ = scaledBalanceOf(RESERVE_TREASURY_ADDRESS());
    mathint ATokenBalance_ = balanceOf(RESERVE_TREASURY_ADDRESS());
    mathint ATokenInternalTotalSupply_ = internalTotalSupply();
    mathint ATokenScaledTotalSupply_ = scaledTotalSupply();
    mathint ATokenTotalSupply_ = totalSupply();
    assert _ATokenInternalBalance == ATokenInternalBalance_ &&
            _ATokenScaledBalance == ATokenScaledBalance_ &&
            _ATokenBalance == ATokenBalance_ &&
            _ATokenInternalTotalSupply == ATokenInternalTotalSupply_ &&
            _ATokenScaledTotalSupply == ATokenScaledTotalSupply_ &&
            _ATokenTotalSupply == ATokenTotalSupply_;
}

/*
    @Rule

    @Description:
        The balance of a receiver in transferOnLiquidation() should increase
        The balance of a sender in transferOnLiquidation() should decrease

    @Formula:
        {
            totalSupplyBefore := totalSupply(),
            balanceOfSenderBefore := balanceOf(sender),
            balanceOfReceiverBefore := balanceOf(receiver),
            
        }

        transferOnLiquidation(sender, receiver, amount)
        
        {
            assert e.msg.sender == LENDING_POOL,
            assert amount != 0 => balanceOfSenderAfter < balanceOfSenderBefore,
            assert amount != 0 => balanceOfReceiverAfter > balanceOfReceiverBefore,
            assert totalSupplyAfter == totalSupplyBefore
        }

    @Note:

    @Link:
*/

rule integrityOfTransferOnLiquidation(address sender, address receiver, uint256 amount) {
    require sender != receiver;
    mathint totalSupplyBefore = totalSupply();
    mathint balanceOfSenderBefore = balanceOf(sender);
    mathint balanceOfReceiverBefore = balanceOf(receiver);
    env e;
    transferOnLiquidation(e, sender, receiver, amount);
    mathint totalSupplyAfter = totalSupply();
    mathint balanceOfSenderAfter = balanceOf(sender);
    mathint balanceOfReceiverAfter = balanceOf(receiver);
    assert e.msg.sender == LENDING_POOL;
    assert amount != 0 => balanceOfSenderAfter < balanceOfSenderBefore;
    assert amount != 0 => balanceOfReceiverAfter > balanceOfReceiverBefore;
    assert totalSupplyAfter == totalSupplyBefore;
}

/*
    @Rule

    @Description:
        burn operation does not change other user's balance

    @Formula:
        {
            _balance := balanceOf(user2),
            _underlyingBalance := UNDERLYING_ASSET.balanceOf(receiverOfUnderlying2)
            
        }

        burn(user1, receiverOfUnderlying, amount, index)
        
        {
            _balance == balanceOf(user2),
            _underlyingBalance == UNDERLYING_ASSET.balanceOf(receiverOfUnderlying2)
        }

    @Note:

    @Link:
*/

rule burnNoInterfernece(address user1, address user2, address receiverOfUnderlying, address receiverOfUnderlying2,
    uint256 amount, uint256 index, uint256 stEthRebasingIndex, uint256 aaveLiquidityIndex)
{
    env e;
    // for onlyLendingPool modifier
    require e.msg.sender == LENDING_POOL;
    uint256 _balance = balanceOf(user2);
    uint256 _underlyingBalance = UNDERLYING_ASSET.balanceOf(receiverOfUnderlying2);
    burn(e, user1, receiverOfUnderlying, amount, index);
    uint256 balance_ = balanceOf(user2);
    uint256 underlyingBalance_ = UNDERLYING_ASSET.balanceOf(receiverOfUnderlying2);

    assert user1!=user2 => _balance==balance_;
    assert receiverOfUnderlying!=receiverOfUnderlying2 && receiverOfUnderlying2!=currentContract =>  _underlyingBalance==underlyingBalance_;
}
