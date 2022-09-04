pragma solidity 0.6.12;
pragma experimental ABIEncoderV2;

import {IAaveIncentivesController} from '../../contracts/interfaces/IAaveIncentivesController.sol';


contract IncentivesControllerMock is IAaveIncentivesController {
  function handleAction(address user, uint256 userBalance, uint256 totalSupply) external override {}
}