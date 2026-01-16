// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract HelloWorld {
    string public greet = "Hello World!";

    function setGreet(string memory _greet) public {
        greet = _greet;
    }
}
