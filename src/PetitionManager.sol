// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

contract PetitionManager {
    // Custom errors for better readability
    error PetitionDoesNotExist();
    error PetitionExpired();
    error AlreadyVoted();
    
    struct Petition {
        string title;
        string description;
        string extendedDescription; // Better name could be "detailedDescription"
        string imageURI; // URI for the image on IPFS
        uint256 votes; // Total votes collected
        uint256 expiry; // Expiry timestamp for the petition
    }

    // Mapping to store petitions
    mapping(uint256 => Petition) public petitions;
    // Mapping to track who has voted on each petition
    mapping(uint256 => mapping(address => bool)) public hasVoted;
    // Counter to keep track of petition IDs
    uint256 public petitionCount;

    // Events for logging
    event PetitionCreated(uint256 indexed petitionId, string title, uint256 expiry);
    event Voted(uint256 indexed petitionId, address voter);

    // Function to create a new petition
    function createPetition(
        string memory _title,
        string memory _description,
        string memory _extendedDescription,
        string memory _imageURI,
        uint256 _duration // Duration in seconds until expiry
    ) public {
        // Calculate expiry timestamp
        uint256 expiry = block.timestamp + _duration;

        // Create a new petition
        petitions[petitionCount] = Petition({
            title: _title,
            description: _description,
            extendedDescription: _extendedDescription,
            imageURI: _imageURI,
            votes: 0,
            expiry: expiry
        });

        emit PetitionCreated(petitionCount, _title, expiry);
        petitionCount++; // Increment the petition count
    }

    // Function to vote on a petition
    function vote(uint256 _petitionId) public {
        // Ensure the petition exists
        if (_petitionId >= petitionCount) revert PetitionDoesNotExist();
        
        // Ensure the petition is not expired
        if (block.timestamp >= petitions[_petitionId].expiry) revert PetitionExpired();
        
        // Prevent double voting
        if (hasVoted[_petitionId][msg.sender]) revert AlreadyVoted();

        // Record the vote
        hasVoted[_petitionId][msg.sender] = true; // Track the user's vote
        petitions[_petitionId].votes++; // Increment the vote count

        emit Voted(_petitionId, msg.sender); // Emit the vote event
    }

    // Function to get the details of a petition
    function getPetition(uint256 _petitionId) public view returns (
        string memory title,
        string memory description,
        string memory extendedDescription,
        string memory imageURI,
        uint256 votes,
        uint256 expiry
    ) {
        // Ensure the petition exists
        if (_petitionId >= petitionCount) revert PetitionDoesNotExist();
        
        Petition storage petition = petitions[_petitionId];

        return (
            petition.title,
            petition.description,
            petition.extendedDescription,
            petition.imageURI,
            petition.votes,
            petition.expiry
        );
    }
}
