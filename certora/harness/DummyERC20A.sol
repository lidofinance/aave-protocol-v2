// SPDX-License-Identifier: agpl-3.0
pragma solidity 0.6.12;
    
import "./DummyERC20Impl.sol";

contract DummyERC20A is DummyERC20Impl {
    function getPooledEthByShares(uint256 _sharesAmount) external view returns (uint256) {
        return 1000000000000000000000000000; // = one RAY
    }
}