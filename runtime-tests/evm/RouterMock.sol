// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

interface IERC20Lite {
    function transferFrom(address from, address to, uint256 amt) external returns (bool);
    function mint(address to, uint256 amt) external;
}

/// Minimal Uniswap V2-shaped router for Vault Anvil. Path length 2 or 3.
contract RouterMock {
    function swapExactTokensForTokens(
        uint256 amountIn,
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256
    ) external returns (uint256[] memory amounts) {
        require(path.length == 2 || path.length == 3, "path");
        uint256 outAmt = amountIn;
        require(outAmt >= amountOutMin, "min");
        require(IERC20Lite(path[0]).transferFrom(msg.sender, address(this), amountIn), "in");
        IERC20Lite(path[path.length - 1]).mint(to, outAmt);
        amounts = new uint256[](path.length);
        amounts[0] = amountIn;
        amounts[path.length - 1] = outAmt;
    }
}
