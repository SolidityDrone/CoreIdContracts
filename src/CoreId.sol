// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import  "./Libraries/UintStringConverter.sol";
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
    function insterUserInfo(
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
}


    