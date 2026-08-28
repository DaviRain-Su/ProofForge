// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

/// Hostile callback fixture for the ProofForge GuardedPayout integration gate.
contract ReentrancyAttacker {
    address public target;
    bool public nestedSucceeded;
    uint256 public callbacks;
    uint256 public observedStatus;

    function attack(address nextTarget) external {
        target = nextTarget;
        nestedSucceeded = true;
        callbacks = 0;
        observedStatus = 0;

        (bool ok, ) = nextTarget.call(
            abi.encodeWithSignature("payout(address,uint256)", address(this), 0)
        );
        require(ok, "outer payout failed");
    }

    receive() external payable {
        callbacks += 1;

        (bool statusOk, bytes memory encodedStatus) = target.staticcall(
            abi.encodeWithSignature("statusOf()")
        );
        require(statusOk && encodedStatus.length == 32, "status read failed");
        observedStatus = abi.decode(encodedStatus, (uint256));

        (nestedSucceeded, ) = target.call(
            abi.encodeWithSignature("payout(address,uint256)", address(this), 0)
        );
    }
}
