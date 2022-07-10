//todo - inhert ERC20 
//add deposit, withdraw, getReserveNormalizedIncome 
pragma solidity 0.6.12;
pragma experimental ABIEncoderV2;

import {SafeERC20} from '../../contracts/dependencies/openzeppelin/contracts/SafeERC20.sol';
import "../../contracts/interfaces/IAToken.sol";
import {Address} from "../../contracts/dependencies/openzeppelin/contracts/Address.sol";

contract SymbolicLendingPool  {

    using SafeERC20 for IERC20;

    address public aToken; 
    uint256 public liquidityIndex = 2; //TODO 
    uint256 public data;
    address public Asset;

    function deposit(
    address asset,
    uint256 amount,
    address onBehalfOf,
    uint16 referralCode
  ) external {
    Asset = asset;
    IERC20(Asset).safeTransferFrom(msg.sender, aToken, amount);
    IAToken(aToken).mint(onBehalfOf, amount,liquidityIndex );
  }


  function withdraw(
    address asset,
    uint256 amount,
    address to
  ) external  returns (uint256) {
    
    IAToken(aToken).burn(msg.sender, to, amount, liquidityIndex);
    return amount;
  }
  
  function getReserveNormalizedIncome(address asset)
    external
    view
    virtual
    returns (uint256) {
      return liquidityIndex;
    }

    function finalizeTransfer(
    address asset,
    address from,
    address to,
    uint256 amount,
    uint256 balanceFromAfter,
    uint256 balanceToBefore
    ) external {
    }

    function getATokenAddress(address asset) public returns (address) {
      return aToken;
    }
} 