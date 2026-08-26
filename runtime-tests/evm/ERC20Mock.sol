// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

/// Minimal ERC-20 mock for Vault Anvil. Not a product token.
contract ERC20Mock {
    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;
    bool public returnFalse;
    bool public noReturn;

    function mint(address to, uint256 amt) external {
        balanceOf[to] += amt;
    }

    function setReturnFalse(bool v) external {
        returnFalse = v;
    }

    function setNoReturn(bool v) external {
        noReturn = v;
    }

    function transfer(address to, uint256 amt) external returns (bool) {
        require(balanceOf[msg.sender] >= amt, "bal");
        balanceOf[msg.sender] -= amt;
        balanceOf[to] += amt;
        return finish();
    }

    function approve(address spender, uint256 amt) external returns (bool) {
        allowance[msg.sender][spender] = amt;
        return finish();
    }

    function transferFrom(address from, address to, uint256 amt) external returns (bool) {
        require(balanceOf[from] >= amt, "bal");
        require(allowance[from][msg.sender] >= amt, "allow");
        allowance[from][msg.sender] -= amt;
        balanceOf[from] -= amt;
        balanceOf[to] += amt;
        return finish();
    }

    function finish() internal returns (bool) {
        if (noReturn) {
            assembly { return(0, 0) }
        }
        if (returnFalse) {
            return false;
        }
        return true;
    }
}
