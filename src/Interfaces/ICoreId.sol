// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

// Import the Permission struct if it's used in the interface.
import { Permission } from "@fhenixprotocol/access/Permissioned.sol";
import { FHE, ebool, inEuint256, euint256} from "@fhenixprotocol/FHE.sol";


interface ICoreId {
    
    // Define events if necessary (optional)
    
    // Function to get user information with a specific permission.
    function getUserInfoWithPermit(
        Permission memory permission,
        address owner
    ) external returns (string memory codiceFiscaleSeal, string memory nameSeal, string memory surnameSeal, string memory pecSeal);
    
    // Function to get user information with permission from either owner or permitted signer.
    function getUserInfoWithPermitBetween(
        Permission memory permission,
        address owner,
        address permitted
    ) external returns (string memory codiceFiscaleSeal, string memory nameSeal, string memory surnameSeal, string memory pecSeal);
    
    // Optional: Function to insert user info (you may want to include it based on your use case).
    function insterUserInfo(
        inEuint256 memory codiceFiscale, 
        inEuint256 memory name, 
        inEuint256 memory surname, 
        inEuint256 memory pec
    ) external;
    
    // Optional: You might also want to expose the `authority` variable if needed
    function authority() external view returns (address);
}