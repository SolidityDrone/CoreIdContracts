// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

library UintStringConverter {
    

    // Function to convert string back to uint 
    // this is a utility function meant to be facilitate translating string to uint
    function stringToUint(string memory input) public pure returns (uint256) {
        uint256 result = 0;
        bytes memory inputBytes = bytes(input);

        // Loop through the input string and convert each character to a uint
        for (uint256 i = 0; i < inputBytes.length; i++) {
            result = result * 256 + uint8(inputBytes[i]);
        }
        return result;
    }

    // Function to convert uint back to string
    // this is a utility function meant to be facilitate translating uint to string
    function uintToString(uint256 input) public pure returns (string memory) {
        // Detect the length of the original string by checking the number of non-zero bytes
        uint256 temp = input;
        uint256 length = 0;

        while (temp != 0) {
            length++;
            temp /= 256;  // Shift the input by 8 bits (1 byte) to count the number of bytes
        }

        // Create a bytes array of the detected length
        bytes memory result = new bytes(length);

        // Extract each byte and convert it back to the original string
        for (uint256 i = length; i > 0; i--) {
            result[i - 1] = bytes1(uint8(input % 256));
            input /= 256;
        }

        return string(result);
    }
}