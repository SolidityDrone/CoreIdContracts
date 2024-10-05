// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import "@fhenixprotocol/access/Permissioned.sol";
import { FHE, ebool, inEuint256, euint256} from "@fhenixprotocol/FHE.sol";


contract CoreId is Permissioned{

    error NotAuthority();

    address public authority;

    mapping (address identityOwner => EUserInfo encryptedUserInfo) internal s_userEncryptedInfos;
    
    struct EUserInfo {
        euint256 codiceFiscale;
        euint256 name;
        euint256 surname;
        euint256 birthday;
    }

    struct SealedOutputs{
        string codiceFiscaleSeal;
        string nameSeal;
        string surnameSeal;
        string birthdaySeal;
    }

    constructor(address _authority) Permissioned() {
        authority = _authority;
    }

    modifier OnlyAuthority(address sender){
        if (sender != authority) revert NotAuthority(); 
        _;
    }

    // this function is just has example values that are relevant. These values are tbd for general purpose
    function insertUserInfo(
        inEuint256 memory codiceFiscale, 
        inEuint256 memory name, 
        inEuint256 memory surname, 
        inEuint256 memory birthday,
        address  userAddress
    ) public OnlyAuthority(msg.sender) {
        s_userEncryptedInfos[userAddress] = EUserInfo({
            codiceFiscale: FHE.asEuint256(codiceFiscale),
            name: FHE.asEuint256(name),
            surname: FHE.asEuint256(surname),
            birthday: FHE.asEuint256(birthday)
        });
    }


    // function that fails if the owner is not the signer
    // The returned data needs to be sanity-checked against the publicFieldHash of an attestation
    // The order to resort hashes it is as it comes
    function getUserInfoWithPermit(
        Permission memory permission,
        address owner
    ) onlyPermitted(permission, owner) public view returns (SealedOutputs memory sealedOutputs){
        EUserInfo memory  eUserInfo = s_userEncryptedInfos[owner];

        sealedOutputs = SealedOutputs({
            codiceFiscaleSeal: FHE.sealoutput(eUserInfo.codiceFiscale, permission.publicKey),
            nameSeal: FHE.sealoutput(eUserInfo.name, permission.publicKey),
            surnameSeal: FHE.sealoutput(eUserInfo.surname, permission.publicKey),
            birthdaySeal: FHE.sealoutput(eUserInfo.birthday, permission.publicKey)
        });
        // implicitly returns sealedOutputs
    }

    // // function that fails if the permitted or owner are not the signers
    // // The returned data needs to be sanity-checked against the publicFieldHash of an attestation
    // // The order to resort hashes it is as it comes
    // function getUserInfoWithPermitBetween(
    //     Permission memory permission,
    //     address owner,
    //     address permitted
    // ) public onlyBetweenPermitted(permission, owner, permitted) returns (SealedOutputs memory sealedOutputs) {
    //     EUserInfo memory eUserInfo = s_userEncryptedInfos[owner];

    //     sealedOutputs = SealedOutputs({
    //         codiceFiscaleSeal: FHE.sealoutput(eUserInfo.codiceFiscale, permission.publicKey),
    //         nameSeal: FHE.sealoutput(eUserInfo.name, permission.publicKey),
    //         surnameSeal: FHE.sealoutput(eUserInfo.surname, permission.publicKey),
    //         birthdaySeal: FHE.sealoutput(eUserInfo.birthday, permission.publicKey)
    //     });
    //     // implicitly returns sealedOutputs
    // }

     
    // Function to convert an array of strings to an array of uint256
    function stringsToUintArray(string[] memory inputs) public pure returns (uint256[] memory) {
        uint256[] memory results = new uint256[](inputs.length);
        
        for (uint256 i = 0; i < inputs.length; i++) {
            results[i] = stringToUint(inputs[i]);
        }
        
        return results;
    }

    // Function to convert a string to uint256
    function stringToUint(string memory input) public pure returns (uint256) {
        uint256 result = 0;
        bytes memory inputBytes = bytes(input);

        // Loop through the input string and convert each character to a uint
        for (uint256 i = 0; i < inputBytes.length; i++) {
            result = result * 256 + uint8(inputBytes[i]);
        }
        return result;
    }

    // Function to convert an array of uint256 to an array of strings
    function uintArrayToStrings(uint256[] memory inputs) public pure returns (string[] memory) {
        string[] memory results = new string[](inputs.length);

        for (uint256 i = 0; i < inputs.length; i++) {
            results[i] = uintToString(inputs[i]);
        }

        return results;
    }

    // Function to convert uint256 back to string
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


    