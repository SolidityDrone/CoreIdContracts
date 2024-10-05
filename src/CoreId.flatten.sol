// SPDX-License-Identifier: MIT
pragma solidity <0.9.0 <=0.8.25 >=0.8.13 >=0.8.19 ^0.8.20 ^0.8.25;

// lib/fhenix-contracts/contracts/FheOS.sol

// solhint-disable one-contract-per-file

library Precompiles {
    //solhint-disable const-name-snakecase
    address public constant Fheos = address(128);
}

interface FheOps {
    function log(string memory s) external pure;
    function add(uint8 utype, bytes memory lhsHash, bytes memory rhsHash) external pure returns (bytes memory);
    function verify(uint8 utype, bytes memory input) external pure returns (bytes memory);
    function sealOutput(uint8 utype, bytes memory ctHash, bytes memory pk) external pure returns (string memory);
    function decrypt(uint8 utype, bytes memory input) external pure returns (uint256);
    function lte(uint8 utype, bytes memory lhsHash, bytes memory rhsHash) external pure returns (bytes memory);
    function sub(uint8 utype, bytes memory lhsHash, bytes memory rhsHash) external pure returns (bytes memory);
    function mul(uint8 utype, bytes memory lhsHash, bytes memory rhsHash) external pure returns (bytes memory);
    function lt(uint8 utype, bytes memory lhsHash, bytes memory rhsHash) external pure returns (bytes memory);
    function select(uint8 utype, bytes memory controlHash, bytes memory ifTrueHash, bytes memory ifFalseHash) external pure returns (bytes memory);
    function req(uint8 utype, bytes memory input) external pure returns (bytes memory);
    function cast(uint8 utype, bytes memory input, uint8 toType) external pure returns (bytes memory);
    function trivialEncrypt(bytes memory input, uint8 toType) external pure returns (bytes memory);
    function div(uint8 utype, bytes memory lhsHash, bytes memory rhsHash) external pure returns (bytes memory);
    function gt(uint8 utype, bytes memory lhsHash, bytes memory rhsHash) external pure returns (bytes memory);
    function gte(uint8 utype, bytes memory lhsHash, bytes memory rhsHash) external pure returns (bytes memory);
    function rem(uint8 utype, bytes memory lhsHash, bytes memory rhsHash) external pure returns (bytes memory);
    function and(uint8 utype, bytes memory lhsHash, bytes memory rhsHash) external pure returns (bytes memory);
    function or(uint8 utype, bytes memory lhsHash, bytes memory rhsHash) external pure returns (bytes memory);
    function xor(uint8 utype, bytes memory lhsHash, bytes memory rhsHash) external pure returns (bytes memory);
    function eq(uint8 utype, bytes memory lhsHash, bytes memory rhsHash) external pure returns (bytes memory);
    function ne(uint8 utype, bytes memory lhsHash, bytes memory rhsHash) external pure returns (bytes memory);
    function min(uint8 utype, bytes memory lhsHash, bytes memory rhsHash) external pure returns (bytes memory);
    function max(uint8 utype, bytes memory lhsHash, bytes memory rhsHash) external pure returns (bytes memory);
    function shl(uint8 utype, bytes memory lhsHash, bytes memory rhsHash) external pure returns (bytes memory);
    function shr(uint8 utype, bytes memory lhsHash, bytes memory rhsHash) external pure returns (bytes memory);
    function not(uint8 utype, bytes memory value) external pure returns (bytes memory);
    function getNetworkPublicKey() external pure returns (bytes memory);
}

// lib/openzeppelin-contracts/contracts/interfaces/IERC5267.sol

// OpenZeppelin Contracts (last updated v5.0.0) (interfaces/IERC5267.sol)

interface IERC5267 {
    /**
     * @dev MAY be emitted to signal that the domain could have changed.
     */
    event EIP712DomainChanged();

    /**
     * @dev returns the fields and values that describe the domain separator used by this contract for EIP-712
     * signature.
     */
    function eip712Domain()
        external
        view
        returns (
            bytes1 fields,
            string memory name,
            string memory version,
            uint256 chainId,
            address verifyingContract,
            bytes32 salt,
            uint256[] memory extensions
        );
}

// lib/openzeppelin-contracts/contracts/utils/StorageSlot.sol

// OpenZeppelin Contracts (last updated v5.0.0) (utils/StorageSlot.sol)
// This file was procedurally generated from scripts/generate/templates/StorageSlot.js.

/**
 * @dev Library for reading and writing primitive types to specific storage slots.
 *
 * Storage slots are often used to avoid storage conflict when dealing with upgradeable contracts.
 * This library helps with reading and writing to such slots without the need for inline assembly.
 *
 * The functions in this library return Slot structs that contain a `value` member that can be used to read or write.
 *
 * Example usage to set ERC1967 implementation slot:
 * ```solidity
 * contract ERC1967 {
 *     bytes32 internal constant _IMPLEMENTATION_SLOT = 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc;
 *
 *     function _getImplementation() internal view returns (address) {
 *         return StorageSlot.getAddressSlot(_IMPLEMENTATION_SLOT).value;
 *     }
 *
 *     function _setImplementation(address newImplementation) internal {
 *         require(newImplementation.code.length > 0);
 *         StorageSlot.getAddressSlot(_IMPLEMENTATION_SLOT).value = newImplementation;
 *     }
 * }
 * ```
 */
library StorageSlot {
    struct AddressSlot {
        address value;
    }

    struct BooleanSlot {
        bool value;
    }

    struct Bytes32Slot {
        bytes32 value;
    }

    struct Uint256Slot {
        uint256 value;
    }

    struct StringSlot {
        string value;
    }

    struct BytesSlot {
        bytes value;
    }

    /**
     * @dev Returns an `AddressSlot` with member `value` located at `slot`.
     */
    function getAddressSlot(bytes32 slot) internal pure returns (AddressSlot storage r) {
        /// @solidity memory-safe-assembly
        assembly {
            r.slot := slot
        }
    }

    /**
     * @dev Returns an `BooleanSlot` with member `value` located at `slot`.
     */
    function getBooleanSlot(bytes32 slot) internal pure returns (BooleanSlot storage r) {
        /// @solidity memory-safe-assembly
        assembly {
            r.slot := slot
        }
    }

    /**
     * @dev Returns an `Bytes32Slot` with member `value` located at `slot`.
     */
    function getBytes32Slot(bytes32 slot) internal pure returns (Bytes32Slot storage r) {
        /// @solidity memory-safe-assembly
        assembly {
            r.slot := slot
        }
    }

    /**
     * @dev Returns an `Uint256Slot` with member `value` located at `slot`.
     */
    function getUint256Slot(bytes32 slot) internal pure returns (Uint256Slot storage r) {
        /// @solidity memory-safe-assembly
        assembly {
            r.slot := slot
        }
    }

    /**
     * @dev Returns an `StringSlot` with member `value` located at `slot`.
     */
    function getStringSlot(bytes32 slot) internal pure returns (StringSlot storage r) {
        /// @solidity memory-safe-assembly
        assembly {
            r.slot := slot
        }
    }

    /**
     * @dev Returns an `StringSlot` representation of the string storage pointer `store`.
     */
    function getStringSlot(string storage store) internal pure returns (StringSlot storage r) {
        /// @solidity memory-safe-assembly
        assembly {
            r.slot := store.slot
        }
    }

    /**
     * @dev Returns an `BytesSlot` with member `value` located at `slot`.
     */
    function getBytesSlot(bytes32 slot) internal pure returns (BytesSlot storage r) {
        /// @solidity memory-safe-assembly
        assembly {
            r.slot := slot
        }
    }

    /**
     * @dev Returns an `BytesSlot` representation of the bytes storage pointer `store`.
     */
    function getBytesSlot(bytes storage store) internal pure returns (BytesSlot storage r) {
        /// @solidity memory-safe-assembly
        assembly {
            r.slot := store.slot
        }
    }
}

// lib/openzeppelin-contracts/contracts/utils/cryptography/ECDSA.sol

// OpenZeppelin Contracts (last updated v5.0.0) (utils/cryptography/ECDSA.sol)

/**
 * @dev Elliptic Curve Digital Signature Algorithm (ECDSA) operations.
 *
 * These functions can be used to verify that a message was signed by the holder
 * of the private keys of a given address.
 */
library ECDSA {
    enum RecoverError {
        NoError,
        InvalidSignature,
        InvalidSignatureLength,
        InvalidSignatureS
    }

    /**
     * @dev The signature derives the `address(0)`.
     */
    error ECDSAInvalidSignature();

    /**
     * @dev The signature has an invalid length.
     */
    error ECDSAInvalidSignatureLength(uint256 length);

    /**
     * @dev The signature has an S value that is in the upper half order.
     */
    error ECDSAInvalidSignatureS(bytes32 s);

    /**
     * @dev Returns the address that signed a hashed message (`hash`) with `signature` or an error. This will not
     * return address(0) without also returning an error description. Errors are documented using an enum (error type)
     * and a bytes32 providing additional information about the error.
     *
     * If no error is returned, then the address can be used for verification purposes.
     *
     * The `ecrecover` EVM precompile allows for malleable (non-unique) signatures:
     * this function rejects them by requiring the `s` value to be in the lower
     * half order, and the `v` value to be either 27 or 28.
     *
     * IMPORTANT: `hash` _must_ be the result of a hash operation for the
     * verification to be secure: it is possible to craft signatures that
     * recover to arbitrary addresses for non-hashed data. A safe way to ensure
     * this is by receiving a hash of the original message (which may otherwise
     * be too long), and then calling {MessageHashUtils-toEthSignedMessageHash} on it.
     *
     * Documentation for signature generation:
     * - with https://web3js.readthedocs.io/en/v1.3.4/web3-eth-accounts.html#sign[Web3.js]
     * - with https://docs.ethers.io/v5/api/signer/#Signer-signMessage[ethers]
     */
    function tryRecover(bytes32 hash, bytes memory signature) internal pure returns (address, RecoverError, bytes32) {
        if (signature.length == 65) {
            bytes32 r;
            bytes32 s;
            uint8 v;
            // ecrecover takes the signature parameters, and the only way to get them
            // currently is to use assembly.
            /// @solidity memory-safe-assembly
            assembly {
                r := mload(add(signature, 0x20))
                s := mload(add(signature, 0x40))
                v := byte(0, mload(add(signature, 0x60)))
            }
            return tryRecover(hash, v, r, s);
        } else {
            return (address(0), RecoverError.InvalidSignatureLength, bytes32(signature.length));
        }
    }

    /**
     * @dev Returns the address that signed a hashed message (`hash`) with
     * `signature`. This address can then be used for verification purposes.
     *
     * The `ecrecover` EVM precompile allows for malleable (non-unique) signatures:
     * this function rejects them by requiring the `s` value to be in the lower
     * half order, and the `v` value to be either 27 or 28.
     *
     * IMPORTANT: `hash` _must_ be the result of a hash operation for the
     * verification to be secure: it is possible to craft signatures that
     * recover to arbitrary addresses for non-hashed data. A safe way to ensure
     * this is by receiving a hash of the original message (which may otherwise
     * be too long), and then calling {MessageHashUtils-toEthSignedMessageHash} on it.
     */
    function recover(bytes32 hash, bytes memory signature) internal pure returns (address) {
        (address recovered, RecoverError error, bytes32 errorArg) = tryRecover(hash, signature);
        _throwError(error, errorArg);
        return recovered;
    }

    /**
     * @dev Overload of {ECDSA-tryRecover} that receives the `r` and `vs` short-signature fields separately.
     *
     * See https://eips.ethereum.org/EIPS/eip-2098[EIP-2098 short signatures]
     */
    function tryRecover(bytes32 hash, bytes32 r, bytes32 vs) internal pure returns (address, RecoverError, bytes32) {
        unchecked {
            bytes32 s = vs & bytes32(0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
            // We do not check for an overflow here since the shift operation results in 0 or 1.
            uint8 v = uint8((uint256(vs) >> 255) + 27);
            return tryRecover(hash, v, r, s);
        }
    }

    /**
     * @dev Overload of {ECDSA-recover} that receives the `r and `vs` short-signature fields separately.
     */
    function recover(bytes32 hash, bytes32 r, bytes32 vs) internal pure returns (address) {
        (address recovered, RecoverError error, bytes32 errorArg) = tryRecover(hash, r, vs);
        _throwError(error, errorArg);
        return recovered;
    }

    /**
     * @dev Overload of {ECDSA-tryRecover} that receives the `v`,
     * `r` and `s` signature fields separately.
     */
    function tryRecover(
        bytes32 hash,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) internal pure returns (address, RecoverError, bytes32) {
        // EIP-2 still allows signature malleability for ecrecover(). Remove this possibility and make the signature
        // unique. Appendix F in the Ethereum Yellow paper (https://ethereum.github.io/yellowpaper/paper.pdf), defines
        // the valid range for s in (301): 0 < s < secp256k1n ÷ 2 + 1, and for v in (302): v ∈ {27, 28}. Most
        // signatures from current libraries generate a unique signature with an s-value in the lower half order.
        //
        // If your library generates malleable signatures, such as s-values in the upper range, calculate a new s-value
        // with 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141 - s1 and flip v from 27 to 28 or
        // vice versa. If your library also generates signatures with 0/1 for v instead 27/28, add 27 to v to accept
        // these malleable signatures as well.
        if (uint256(s) > 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0) {
            return (address(0), RecoverError.InvalidSignatureS, s);
        }

        // If the signature is valid (and not malleable), return the signer address
        address signer = ecrecover(hash, v, r, s);
        if (signer == address(0)) {
            return (address(0), RecoverError.InvalidSignature, bytes32(0));
        }

        return (signer, RecoverError.NoError, bytes32(0));
    }

    /**
     * @dev Overload of {ECDSA-recover} that receives the `v`,
     * `r` and `s` signature fields separately.
     */
    function recover(bytes32 hash, uint8 v, bytes32 r, bytes32 s) internal pure returns (address) {
        (address recovered, RecoverError error, bytes32 errorArg) = tryRecover(hash, v, r, s);
        _throwError(error, errorArg);
        return recovered;
    }

    /**
     * @dev Optionally reverts with the corresponding custom error according to the `error` argument provided.
     */
    function _throwError(RecoverError error, bytes32 errorArg) private pure {
        if (error == RecoverError.NoError) {
            return; // no error: do nothing
        } else if (error == RecoverError.InvalidSignature) {
            revert ECDSAInvalidSignature();
        } else if (error == RecoverError.InvalidSignatureLength) {
            revert ECDSAInvalidSignatureLength(uint256(errorArg));
        } else if (error == RecoverError.InvalidSignatureS) {
            revert ECDSAInvalidSignatureS(errorArg);
        }
    }
}

// lib/openzeppelin-contracts/contracts/utils/math/Math.sol

// OpenZeppelin Contracts (last updated v5.0.0) (utils/math/Math.sol)

/**
 * @dev Standard math utilities missing in the Solidity language.
 */
library Math {
    /**
     * @dev Muldiv operation overflow.
     */
    error MathOverflowedMulDiv();

    enum Rounding {
        Floor, // Toward negative infinity
        Ceil, // Toward positive infinity
        Trunc, // Toward zero
        Expand // Away from zero
    }

    /**
     * @dev Returns the addition of two unsigned integers, with an overflow flag.
     */
    function tryAdd(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            uint256 c = a + b;
            if (c < a) return (false, 0);
            return (true, c);
        }
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, with an overflow flag.
     */
    function trySub(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            if (b > a) return (false, 0);
            return (true, a - b);
        }
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, with an overflow flag.
     */
    function tryMul(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
            // benefit is lost if 'b' is also tested.
            // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
            if (a == 0) return (true, 0);
            uint256 c = a * b;
            if (c / a != b) return (false, 0);
            return (true, c);
        }
    }

    /**
     * @dev Returns the division of two unsigned integers, with a division by zero flag.
     */
    function tryDiv(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            if (b == 0) return (false, 0);
            return (true, a / b);
        }
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers, with a division by zero flag.
     */
    function tryMod(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            if (b == 0) return (false, 0);
            return (true, a % b);
        }
    }

    /**
     * @dev Returns the largest of two numbers.
     */
    function max(uint256 a, uint256 b) internal pure returns (uint256) {
        return a > b ? a : b;
    }

    /**
     * @dev Returns the smallest of two numbers.
     */
    function min(uint256 a, uint256 b) internal pure returns (uint256) {
        return a < b ? a : b;
    }

    /**
     * @dev Returns the average of two numbers. The result is rounded towards
     * zero.
     */
    function average(uint256 a, uint256 b) internal pure returns (uint256) {
        // (a + b) / 2 can overflow.
        return (a & b) + (a ^ b) / 2;
    }

    /**
     * @dev Returns the ceiling of the division of two numbers.
     *
     * This differs from standard division with `/` in that it rounds towards infinity instead
     * of rounding towards zero.
     */
    function ceilDiv(uint256 a, uint256 b) internal pure returns (uint256) {
        if (b == 0) {
            // Guarantee the same behavior as in a regular Solidity division.
            return a / b;
        }

        // (a + b - 1) / b can overflow on addition, so we distribute.
        return a == 0 ? 0 : (a - 1) / b + 1;
    }

    /**
     * @notice Calculates floor(x * y / denominator) with full precision. Throws if result overflows a uint256 or
     * denominator == 0.
     * @dev Original credit to Remco Bloemen under MIT license (https://xn--2-umb.com/21/muldiv) with further edits by
     * Uniswap Labs also under MIT license.
     */
    function mulDiv(uint256 x, uint256 y, uint256 denominator) internal pure returns (uint256 result) {
        unchecked {
            // 512-bit multiply [prod1 prod0] = x * y. Compute the product mod 2^256 and mod 2^256 - 1, then use
            // use the Chinese Remainder Theorem to reconstruct the 512 bit result. The result is stored in two 256
            // variables such that product = prod1 * 2^256 + prod0.
            uint256 prod0 = x * y; // Least significant 256 bits of the product
            uint256 prod1; // Most significant 256 bits of the product
            assembly {
                let mm := mulmod(x, y, not(0))
                prod1 := sub(sub(mm, prod0), lt(mm, prod0))
            }

            // Handle non-overflow cases, 256 by 256 division.
            if (prod1 == 0) {
                // Solidity will revert if denominator == 0, unlike the div opcode on its own.
                // The surrounding unchecked block does not change this fact.
                // See https://docs.soliditylang.org/en/latest/control-structures.html#checked-or-unchecked-arithmetic.
                return prod0 / denominator;
            }

            // Make sure the result is less than 2^256. Also prevents denominator == 0.
            if (denominator <= prod1) {
                revert MathOverflowedMulDiv();
            }

            ///////////////////////////////////////////////
            // 512 by 256 division.
            ///////////////////////////////////////////////

            // Make division exact by subtracting the remainder from [prod1 prod0].
            uint256 remainder;
            assembly {
                // Compute remainder using mulmod.
                remainder := mulmod(x, y, denominator)

                // Subtract 256 bit number from 512 bit number.
                prod1 := sub(prod1, gt(remainder, prod0))
                prod0 := sub(prod0, remainder)
            }

            // Factor powers of two out of denominator and compute largest power of two divisor of denominator.
            // Always >= 1. See https://cs.stackexchange.com/q/138556/92363.

            uint256 twos = denominator & (0 - denominator);
            assembly {
                // Divide denominator by twos.
                denominator := div(denominator, twos)

                // Divide [prod1 prod0] by twos.
                prod0 := div(prod0, twos)

                // Flip twos such that it is 2^256 / twos. If twos is zero, then it becomes one.
                twos := add(div(sub(0, twos), twos), 1)
            }

            // Shift in bits from prod1 into prod0.
            prod0 |= prod1 * twos;

            // Invert denominator mod 2^256. Now that denominator is an odd number, it has an inverse modulo 2^256 such
            // that denominator * inv = 1 mod 2^256. Compute the inverse by starting with a seed that is correct for
            // four bits. That is, denominator * inv = 1 mod 2^4.
            uint256 inverse = (3 * denominator) ^ 2;

            // Use the Newton-Raphson iteration to improve the precision. Thanks to Hensel's lifting lemma, this also
            // works in modular arithmetic, doubling the correct bits in each step.
            inverse *= 2 - denominator * inverse; // inverse mod 2^8
            inverse *= 2 - denominator * inverse; // inverse mod 2^16
            inverse *= 2 - denominator * inverse; // inverse mod 2^32
            inverse *= 2 - denominator * inverse; // inverse mod 2^64
            inverse *= 2 - denominator * inverse; // inverse mod 2^128
            inverse *= 2 - denominator * inverse; // inverse mod 2^256

            // Because the division is now exact we can divide by multiplying with the modular inverse of denominator.
            // This will give us the correct result modulo 2^256. Since the preconditions guarantee that the outcome is
            // less than 2^256, this is the final result. We don't need to compute the high bits of the result and prod1
            // is no longer required.
            result = prod0 * inverse;
            return result;
        }
    }

    /**
     * @notice Calculates x * y / denominator with full precision, following the selected rounding direction.
     */
    function mulDiv(uint256 x, uint256 y, uint256 denominator, Rounding rounding) internal pure returns (uint256) {
        uint256 result = mulDiv(x, y, denominator);
        if (unsignedRoundsUp(rounding) && mulmod(x, y, denominator) > 0) {
            result += 1;
        }
        return result;
    }

    /**
     * @dev Returns the square root of a number. If the number is not a perfect square, the value is rounded
     * towards zero.
     *
     * Inspired by Henry S. Warren, Jr.'s "Hacker's Delight" (Chapter 11).
     */
    function sqrt(uint256 a) internal pure returns (uint256) {
        if (a == 0) {
            return 0;
        }

        // For our first guess, we get the biggest power of 2 which is smaller than the square root of the target.
        //
        // We know that the "msb" (most significant bit) of our target number `a` is a power of 2 such that we have
        // `msb(a) <= a < 2*msb(a)`. This value can be written `msb(a)=2**k` with `k=log2(a)`.
        //
        // This can be rewritten `2**log2(a) <= a < 2**(log2(a) + 1)`
        // → `sqrt(2**k) <= sqrt(a) < sqrt(2**(k+1))`
        // → `2**(k/2) <= sqrt(a) < 2**((k+1)/2) <= 2**(k/2 + 1)`
        //
        // Consequently, `2**(log2(a) / 2)` is a good first approximation of `sqrt(a)` with at least 1 correct bit.
        uint256 result = 1 << (log2(a) >> 1);

        // At this point `result` is an estimation with one bit of precision. We know the true value is a uint128,
        // since it is the square root of a uint256. Newton's method converges quadratically (precision doubles at
        // every iteration). We thus need at most 7 iteration to turn our partial result with one bit of precision
        // into the expected uint128 result.
        unchecked {
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            return min(result, a / result);
        }
    }

    /**
     * @notice Calculates sqrt(a), following the selected rounding direction.
     */
    function sqrt(uint256 a, Rounding rounding) internal pure returns (uint256) {
        unchecked {
            uint256 result = sqrt(a);
            return result + (unsignedRoundsUp(rounding) && result * result < a ? 1 : 0);
        }
    }

    /**
     * @dev Return the log in base 2 of a positive value rounded towards zero.
     * Returns 0 if given 0.
     */
    function log2(uint256 value) internal pure returns (uint256) {
        uint256 result = 0;
        unchecked {
            if (value >> 128 > 0) {
                value >>= 128;
                result += 128;
            }
            if (value >> 64 > 0) {
                value >>= 64;
                result += 64;
            }
            if (value >> 32 > 0) {
                value >>= 32;
                result += 32;
            }
            if (value >> 16 > 0) {
                value >>= 16;
                result += 16;
            }
            if (value >> 8 > 0) {
                value >>= 8;
                result += 8;
            }
            if (value >> 4 > 0) {
                value >>= 4;
                result += 4;
            }
            if (value >> 2 > 0) {
                value >>= 2;
                result += 2;
            }
            if (value >> 1 > 0) {
                result += 1;
            }
        }
        return result;
    }

    /**
     * @dev Return the log in base 2, following the selected rounding direction, of a positive value.
     * Returns 0 if given 0.
     */
    function log2(uint256 value, Rounding rounding) internal pure returns (uint256) {
        unchecked {
            uint256 result = log2(value);
            return result + (unsignedRoundsUp(rounding) && 1 << result < value ? 1 : 0);
        }
    }

    /**
     * @dev Return the log in base 10 of a positive value rounded towards zero.
     * Returns 0 if given 0.
     */
    function log10(uint256 value) internal pure returns (uint256) {
        uint256 result = 0;
        unchecked {
            if (value >= 10 ** 64) {
                value /= 10 ** 64;
                result += 64;
            }
            if (value >= 10 ** 32) {
                value /= 10 ** 32;
                result += 32;
            }
            if (value >= 10 ** 16) {
                value /= 10 ** 16;
                result += 16;
            }
            if (value >= 10 ** 8) {
                value /= 10 ** 8;
                result += 8;
            }
            if (value >= 10 ** 4) {
                value /= 10 ** 4;
                result += 4;
            }
            if (value >= 10 ** 2) {
                value /= 10 ** 2;
                result += 2;
            }
            if (value >= 10 ** 1) {
                result += 1;
            }
        }
        return result;
    }

    /**
     * @dev Return the log in base 10, following the selected rounding direction, of a positive value.
     * Returns 0 if given 0.
     */
    function log10(uint256 value, Rounding rounding) internal pure returns (uint256) {
        unchecked {
            uint256 result = log10(value);
            return result + (unsignedRoundsUp(rounding) && 10 ** result < value ? 1 : 0);
        }
    }

    /**
     * @dev Return the log in base 256 of a positive value rounded towards zero.
     * Returns 0 if given 0.
     *
     * Adding one to the result gives the number of pairs of hex symbols needed to represent `value` as a hex string.
     */
    function log256(uint256 value) internal pure returns (uint256) {
        uint256 result = 0;
        unchecked {
            if (value >> 128 > 0) {
                value >>= 128;
                result += 16;
            }
            if (value >> 64 > 0) {
                value >>= 64;
                result += 8;
            }
            if (value >> 32 > 0) {
                value >>= 32;
                result += 4;
            }
            if (value >> 16 > 0) {
                value >>= 16;
                result += 2;
            }
            if (value >> 8 > 0) {
                result += 1;
            }
        }
        return result;
    }

    /**
     * @dev Return the log in base 256, following the selected rounding direction, of a positive value.
     * Returns 0 if given 0.
     */
    function log256(uint256 value, Rounding rounding) internal pure returns (uint256) {
        unchecked {
            uint256 result = log256(value);
            return result + (unsignedRoundsUp(rounding) && 1 << (result << 3) < value ? 1 : 0);
        }
    }

    /**
     * @dev Returns whether a provided rounding mode is considered rounding up for unsigned integers.
     */
    function unsignedRoundsUp(Rounding rounding) internal pure returns (bool) {
        return uint8(rounding) % 2 == 1;
    }
}

// lib/openzeppelin-contracts/contracts/utils/math/SignedMath.sol

// OpenZeppelin Contracts (last updated v5.0.0) (utils/math/SignedMath.sol)

/**
 * @dev Standard signed math utilities missing in the Solidity language.
 */
library SignedMath {
    /**
     * @dev Returns the largest of two signed numbers.
     */
    function max(int256 a, int256 b) internal pure returns (int256) {
        return a > b ? a : b;
    }

    /**
     * @dev Returns the smallest of two signed numbers.
     */
    function min(int256 a, int256 b) internal pure returns (int256) {
        return a < b ? a : b;
    }

    /**
     * @dev Returns the average of two signed numbers without overflow.
     * The result is rounded towards zero.
     */
    function average(int256 a, int256 b) internal pure returns (int256) {
        // Formula from the book "Hacker's Delight"
        int256 x = (a & b) + ((a ^ b) >> 1);
        return x + (int256(uint256(x) >> 255) & (a ^ b));
    }

    /**
     * @dev Returns the absolute unsigned value of a signed value.
     */
    function abs(int256 n) internal pure returns (uint256) {
        unchecked {
            // must be unchecked in order to support `n = type(int256).min`
            return uint256(n >= 0 ? n : -n);
        }
    }
}

// src/Libraries/UintStringConverter.sol



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

// lib/fhenix-contracts/contracts/FHE.sol

// solhint-disable one-contract-per-file

type ebool is uint256;
type euint8 is uint256;
type euint16 is uint256;
type euint32 is uint256;
type euint64 is uint256;
type euint128 is uint256;
type euint256 is uint256;
type eaddress is uint256;

struct inEbool {
    bytes data;
}
struct inEuint8 {
    bytes data;
}
struct inEuint16 {
    bytes data;
}
struct inEuint32 {
    bytes data;
}
struct inEuint64 {
    bytes data;
}
struct inEuint128 {
    bytes data;
}
struct inEuint256 {
    bytes data;
}
struct inEaddress {
    bytes data;
}

struct SealedArray {
  bytes[] data;
}

library Common {
    // Values used to communicate types to the runtime.
    // Must match values defined in warp-drive protobufs for everything to 
    // make sense
    uint8 internal constant EUINT8_TFHE = 0;
    uint8 internal constant EUINT16_TFHE = 1;
    uint8 internal constant EUINT32_TFHE = 2;
    uint8 internal constant EUINT64_TFHE = 3;
    uint8 internal constant EUINT128_TFHE = 4;
    uint8 internal constant EUINT256_TFHE = 5;
    uint8 internal constant EADDRESS_TFHE = 12;
    // uint8 internal constant INT_BGV = 12;
    uint8 internal constant EBOOL_TFHE = 13;
    
    function bigIntToBool(uint256 i) internal pure returns (bool) {
        return (i > 0);
    }

    function bigIntToUint8(uint256 i) internal pure returns (uint8) {
        return uint8(i);
    }

    function bigIntToUint16(uint256 i) internal pure returns (uint16) {
        return uint16(i);
    }

    function bigIntToUint32(uint256 i) internal pure returns (uint32) {
        return uint32(i);
    }

    function bigIntToUint64(uint256 i) internal pure returns (uint64) {
        return uint64(i);
    }

    function bigIntToUint128(uint256 i) internal pure returns (uint128) {
        return uint128(i);
    }

    function bigIntToUint256(uint256 i) internal pure returns (uint256) {
        return i;
    }

    function bigIntToAddress(uint256 i) internal pure returns (address) {
      return address(uint160(i));
    }
    
    function toBytes(uint256 x) internal pure returns (bytes memory b) {
        b = new bytes(32);
        assembly { mstore(add(b, 32), x) }
    }
}

library Impl {
    function sealoutput(uint8 utype, uint256 ciphertext, bytes32 publicKey) internal pure returns (string memory reencrypted) {
        // Call the sealoutput precompile.
        reencrypted = FheOps(Precompiles.Fheos).sealOutput(utype, Common.toBytes(ciphertext), bytes.concat(publicKey));

        return reencrypted;
    }

    function verify(bytes memory _ciphertextBytes, uint8 _toType) internal pure returns (uint256 result) {
        bytes memory output;

        // Call the verify precompile.
        output = FheOps(Precompiles.Fheos).verify(_toType, _ciphertextBytes);
        result = getValue(output);
    }

    function cast(uint8 utype, uint256 ciphertext, uint8 toType) internal pure returns (uint256 result) {
        bytes memory output;

        // Call the cast precompile.
        output = FheOps(Precompiles.Fheos).cast(utype, Common.toBytes(ciphertext), toType);
        result = getValue(output);
    }

    function getValue(bytes memory a) internal pure returns (uint256 value) {
        assembly {
            value := mload(add(a, 0x20))
        }
    }

    function trivialEncrypt(uint256 value, uint8 toType) internal pure returns (uint256 result) {
        bytes memory output;

        // Call the trivialEncrypt precompile.
        output = FheOps(Precompiles.Fheos).trivialEncrypt(Common.toBytes(value), toType);

        result = getValue(output);
    }

    function select(uint8 utype, uint256 control, uint256 ifTrue, uint256 ifFalse) internal pure returns (uint256 result) {
        bytes memory output;

        // Call the trivialEncrypt precompile.
        output = FheOps(Precompiles.Fheos).select(utype, Common.toBytes(control), Common.toBytes(ifTrue), Common.toBytes(ifFalse));

        result = getValue(output);
    }
}

library FHE {
    euint8 public constant NIL8 = euint8.wrap(0);
    euint16 public constant NIL16 = euint16.wrap(0);
    euint32 public constant NIL32 = euint32.wrap(0);

    // Return true if the encrypted integer is initialized and false otherwise.
    function isInitialized(ebool v) internal pure returns (bool) {
        return ebool.unwrap(v) != 0;
    }

    // Return true if the encrypted integer is initialized and false otherwise.
    function isInitialized(euint8 v) internal pure returns (bool) {
        return euint8.unwrap(v) != 0;
    }

    // Return true if the encrypted integer is initialized and false otherwise.
    function isInitialized(euint16 v) internal pure returns (bool) {
        return euint16.unwrap(v) != 0;
    }

    // Return true if the encrypted integer is initialized and false otherwise.
    function isInitialized(euint32 v) internal pure returns (bool) {
        return euint32.unwrap(v) != 0;
    }
    
    // Return true if the encrypted integer is initialized and false otherwise.
    function isInitialized(euint64 v) internal pure returns (bool) {
        return euint64.unwrap(v) != 0;
    }
    
        // Return true if the encrypted integer is initialized and false otherwise.
    function isInitialized(euint128 v) internal pure returns (bool) {
        return euint128.unwrap(v) != 0;
    }
    
        // Return true if the encrypted integer is initialized and false otherwise.
    function isInitialized(euint256 v) internal pure returns (bool) {
        return euint256.unwrap(v) != 0;
    }

    function isInitialized(eaddress v) internal pure returns (bool) {
        return eaddress.unwrap(v) != 0;
    }

    function getValue(bytes memory a) private pure returns (uint256 value) {
        assembly {
            value := mload(add(a, 0x20))
        }
    }
    
    function mathHelper(
        uint8 utype,
        uint256 lhs,
        uint256 rhs,
        function(uint8, bytes memory, bytes memory) external pure returns (bytes memory) impl
    ) internal pure returns (uint256 result) {
        bytes memory output;
        output = impl(utype, Common.toBytes(lhs), Common.toBytes(rhs));
        result = getValue(output);
    }
    
    /// @notice This functions performs the add operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function add(euint8 lhs, euint8 rhs) internal pure returns (euint8) {
        if (!isInitialized(lhs)) {
            lhs = asEuint8(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint8(0);
        }
        uint256 unwrappedInput1 = euint8.unwrap(lhs);
        uint256 unwrappedInput2 = euint8.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT8_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).add);
        return euint8.wrap(result);
    }
    /// @notice This functions performs the add operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function add(euint16 lhs, euint16 rhs) internal pure returns (euint16) {
        if (!isInitialized(lhs)) {
            lhs = asEuint16(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint16(0);
        }
        uint256 unwrappedInput1 = euint16.unwrap(lhs);
        uint256 unwrappedInput2 = euint16.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT16_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).add);
        return euint16.wrap(result);
    }
    /// @notice This functions performs the add operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function add(euint32 lhs, euint32 rhs) internal pure returns (euint32) {
        if (!isInitialized(lhs)) {
            lhs = asEuint32(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint32(0);
        }
        uint256 unwrappedInput1 = euint32.unwrap(lhs);
        uint256 unwrappedInput2 = euint32.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT32_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).add);
        return euint32.wrap(result);
    }
    /// @notice This functions performs the add operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function add(euint64 lhs, euint64 rhs) internal pure returns (euint64) {
        if (!isInitialized(lhs)) {
            lhs = asEuint64(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint64(0);
        }
        uint256 unwrappedInput1 = euint64.unwrap(lhs);
        uint256 unwrappedInput2 = euint64.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT64_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).add);
        return euint64.wrap(result);
    }
    /// @notice This functions performs the add operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function add(euint128 lhs, euint128 rhs) internal pure returns (euint128) {
        if (!isInitialized(lhs)) {
            lhs = asEuint128(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint128(0);
        }
        uint256 unwrappedInput1 = euint128.unwrap(lhs);
        uint256 unwrappedInput2 = euint128.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT128_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).add);
        return euint128.wrap(result);
    }
    /// @notice performs the sealoutput function on a ebool ciphertext. This operation returns the plaintext value, sealed for the public key provided 
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param value Ciphertext to decrypt and seal
    /// @param publicKey Public Key that will receive the sealed plaintext
    /// @return Plaintext input, sealed for the owner of `publicKey`
    function sealoutput(ebool value, bytes32 publicKey) internal pure returns (string memory) {
        if (!isInitialized(value)) {
            value = asEbool(0);
        }
        uint256 unwrapped = ebool.unwrap(value);

        return Impl.sealoutput(Common.EBOOL_TFHE, unwrapped, publicKey);
    }
    /// @notice performs the sealoutput function on a euint8 ciphertext. This operation returns the plaintext value, sealed for the public key provided 
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param value Ciphertext to decrypt and seal
    /// @param publicKey Public Key that will receive the sealed plaintext
    /// @return Plaintext input, sealed for the owner of `publicKey`
    function sealoutput(euint8 value, bytes32 publicKey) internal pure returns (string memory) {
        if (!isInitialized(value)) {
            value = asEuint8(0);
        }
        uint256 unwrapped = euint8.unwrap(value);

        return Impl.sealoutput(Common.EUINT8_TFHE, unwrapped, publicKey);
    }
    /// @notice performs the sealoutput function on a euint16 ciphertext. This operation returns the plaintext value, sealed for the public key provided 
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param value Ciphertext to decrypt and seal
    /// @param publicKey Public Key that will receive the sealed plaintext
    /// @return Plaintext input, sealed for the owner of `publicKey`
    function sealoutput(euint16 value, bytes32 publicKey) internal pure returns (string memory) {
        if (!isInitialized(value)) {
            value = asEuint16(0);
        }
        uint256 unwrapped = euint16.unwrap(value);

        return Impl.sealoutput(Common.EUINT16_TFHE, unwrapped, publicKey);
    }
    /// @notice performs the sealoutput function on a euint32 ciphertext. This operation returns the plaintext value, sealed for the public key provided 
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param value Ciphertext to decrypt and seal
    /// @param publicKey Public Key that will receive the sealed plaintext
    /// @return Plaintext input, sealed for the owner of `publicKey`
    function sealoutput(euint32 value, bytes32 publicKey) internal pure returns (string memory) {
        if (!isInitialized(value)) {
            value = asEuint32(0);
        }
        uint256 unwrapped = euint32.unwrap(value);

        return Impl.sealoutput(Common.EUINT32_TFHE, unwrapped, publicKey);
    }
    /// @notice performs the sealoutput function on a euint64 ciphertext. This operation returns the plaintext value, sealed for the public key provided 
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param value Ciphertext to decrypt and seal
    /// @param publicKey Public Key that will receive the sealed plaintext
    /// @return Plaintext input, sealed for the owner of `publicKey`
    function sealoutput(euint64 value, bytes32 publicKey) internal pure returns (string memory) {
        if (!isInitialized(value)) {
            value = asEuint64(0);
        }
        uint256 unwrapped = euint64.unwrap(value);

        return Impl.sealoutput(Common.EUINT64_TFHE, unwrapped, publicKey);
    }
    /// @notice performs the sealoutput function on a euint128 ciphertext. This operation returns the plaintext value, sealed for the public key provided 
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param value Ciphertext to decrypt and seal
    /// @param publicKey Public Key that will receive the sealed plaintext
    /// @return Plaintext input, sealed for the owner of `publicKey`
    function sealoutput(euint128 value, bytes32 publicKey) internal pure returns (string memory) {
        if (!isInitialized(value)) {
            value = asEuint128(0);
        }
        uint256 unwrapped = euint128.unwrap(value);

        return Impl.sealoutput(Common.EUINT128_TFHE, unwrapped, publicKey);
    }
    /// @notice performs the sealoutput function on a euint256 ciphertext. This operation returns the plaintext value, sealed for the public key provided 
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param value Ciphertext to decrypt and seal
    /// @param publicKey Public Key that will receive the sealed plaintext
    /// @return Plaintext input, sealed for the owner of `publicKey`
    function sealoutput(euint256 value, bytes32 publicKey) internal pure returns (string memory) {
        if (!isInitialized(value)) {
            value = asEuint256(0);
        }
        uint256 unwrapped = euint256.unwrap(value);

        return Impl.sealoutput(Common.EUINT256_TFHE, unwrapped, publicKey);
    }
    /// @notice performs the sealoutput function on a eaddress ciphertext. This operation returns the plaintext value, sealed for the public key provided 
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param value Ciphertext to decrypt and seal
    /// @param publicKey Public Key that will receive the sealed plaintext
    /// @return Plaintext input, sealed for the owner of `publicKey`
    function sealoutput(eaddress value, bytes32 publicKey) internal pure returns (string memory) {
        if (!isInitialized(value)) {
            value = asEaddress(0);
        }
        uint256 unwrapped = eaddress.unwrap(value);

        return Impl.sealoutput(Common.EADDRESS_TFHE, unwrapped, publicKey);
    }
    /// @notice Performs the decrypt operation on a ciphertext
    /// @dev Verifies that the input value matches a valid ciphertext. Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param input1 the input ciphertext
    function decrypt(ebool input1) internal pure returns (bool) {
        if (!isInitialized(input1)) {
            input1 = asEbool(0);
        }
        uint256 unwrappedInput1 = ebool.unwrap(input1);
        bytes memory inputAsBytes = Common.toBytes(unwrappedInput1);
        uint256 result = FheOps(Precompiles.Fheos).decrypt(Common.EBOOL_TFHE, inputAsBytes);
        return Common.bigIntToBool(result);
    }
    /// @notice Performs the decrypt operation on a ciphertext
    /// @dev Verifies that the input value matches a valid ciphertext. Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param input1 the input ciphertext
    function decrypt(euint8 input1) internal pure returns (uint8) {
        if (!isInitialized(input1)) {
            input1 = asEuint8(0);
        }
        uint256 unwrappedInput1 = euint8.unwrap(input1);
        bytes memory inputAsBytes = Common.toBytes(unwrappedInput1);
        uint256 result = FheOps(Precompiles.Fheos).decrypt(Common.EUINT8_TFHE, inputAsBytes);
        return Common.bigIntToUint8(result);
    }
    /// @notice Performs the decrypt operation on a ciphertext
    /// @dev Verifies that the input value matches a valid ciphertext. Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param input1 the input ciphertext
    function decrypt(euint16 input1) internal pure returns (uint16) {
        if (!isInitialized(input1)) {
            input1 = asEuint16(0);
        }
        uint256 unwrappedInput1 = euint16.unwrap(input1);
        bytes memory inputAsBytes = Common.toBytes(unwrappedInput1);
        uint256 result = FheOps(Precompiles.Fheos).decrypt(Common.EUINT16_TFHE, inputAsBytes);
        return Common.bigIntToUint16(result);
    }
    /// @notice Performs the decrypt operation on a ciphertext
    /// @dev Verifies that the input value matches a valid ciphertext. Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param input1 the input ciphertext
    function decrypt(euint32 input1) internal pure returns (uint32) {
        if (!isInitialized(input1)) {
            input1 = asEuint32(0);
        }
        uint256 unwrappedInput1 = euint32.unwrap(input1);
        bytes memory inputAsBytes = Common.toBytes(unwrappedInput1);
        uint256 result = FheOps(Precompiles.Fheos).decrypt(Common.EUINT32_TFHE, inputAsBytes);
        return Common.bigIntToUint32(result);
    }
    /// @notice Performs the decrypt operation on a ciphertext
    /// @dev Verifies that the input value matches a valid ciphertext. Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param input1 the input ciphertext
    function decrypt(euint64 input1) internal pure returns (uint64) {
        if (!isInitialized(input1)) {
            input1 = asEuint64(0);
        }
        uint256 unwrappedInput1 = euint64.unwrap(input1);
        bytes memory inputAsBytes = Common.toBytes(unwrappedInput1);
        uint256 result = FheOps(Precompiles.Fheos).decrypt(Common.EUINT64_TFHE, inputAsBytes);
        return Common.bigIntToUint64(result);
    }
    /// @notice Performs the decrypt operation on a ciphertext
    /// @dev Verifies that the input value matches a valid ciphertext. Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param input1 the input ciphertext
    function decrypt(euint128 input1) internal pure returns (uint128) {
        if (!isInitialized(input1)) {
            input1 = asEuint128(0);
        }
        uint256 unwrappedInput1 = euint128.unwrap(input1);
        bytes memory inputAsBytes = Common.toBytes(unwrappedInput1);
        uint256 result = FheOps(Precompiles.Fheos).decrypt(Common.EUINT128_TFHE, inputAsBytes);
        return Common.bigIntToUint128(result);
    }
    /// @notice Performs the decrypt operation on a ciphertext
    /// @dev Verifies that the input value matches a valid ciphertext. Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param input1 the input ciphertext
    function decrypt(euint256 input1) internal pure returns (uint256) {
        if (!isInitialized(input1)) {
            input1 = asEuint256(0);
        }
        uint256 unwrappedInput1 = euint256.unwrap(input1);
        bytes memory inputAsBytes = Common.toBytes(unwrappedInput1);
        uint256 result = FheOps(Precompiles.Fheos).decrypt(Common.EUINT256_TFHE, inputAsBytes);
        return Common.bigIntToUint256(result);
    }
    /// @notice Performs the decrypt operation on a ciphertext
    /// @dev Verifies that the input value matches a valid ciphertext. Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param input1 the input ciphertext
    function decrypt(eaddress input1) internal pure returns (address) {
        if (!isInitialized(input1)) {
            input1 = asEaddress(0);
        }
        uint256 unwrappedInput1 = eaddress.unwrap(input1);
        bytes memory inputAsBytes = Common.toBytes(unwrappedInput1);
        uint256 result = FheOps(Precompiles.Fheos).decrypt(Common.EADDRESS_TFHE, inputAsBytes);
        return Common.bigIntToAddress(result);
    }
    /// @notice This functions performs the lte operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function lte(euint8 lhs, euint8 rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEuint8(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint8(0);
        }
        uint256 unwrappedInput1 = euint8.unwrap(lhs);
        uint256 unwrappedInput2 = euint8.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT8_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).lte);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the lte operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function lte(euint16 lhs, euint16 rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEuint16(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint16(0);
        }
        uint256 unwrappedInput1 = euint16.unwrap(lhs);
        uint256 unwrappedInput2 = euint16.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT16_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).lte);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the lte operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function lte(euint32 lhs, euint32 rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEuint32(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint32(0);
        }
        uint256 unwrappedInput1 = euint32.unwrap(lhs);
        uint256 unwrappedInput2 = euint32.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT32_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).lte);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the lte operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function lte(euint64 lhs, euint64 rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEuint64(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint64(0);
        }
        uint256 unwrappedInput1 = euint64.unwrap(lhs);
        uint256 unwrappedInput2 = euint64.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT64_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).lte);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the lte operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function lte(euint128 lhs, euint128 rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEuint128(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint128(0);
        }
        uint256 unwrappedInput1 = euint128.unwrap(lhs);
        uint256 unwrappedInput2 = euint128.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT128_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).lte);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the sub operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function sub(euint8 lhs, euint8 rhs) internal pure returns (euint8) {
        if (!isInitialized(lhs)) {
            lhs = asEuint8(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint8(0);
        }
        uint256 unwrappedInput1 = euint8.unwrap(lhs);
        uint256 unwrappedInput2 = euint8.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT8_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).sub);
        return euint8.wrap(result);
    }
    /// @notice This functions performs the sub operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function sub(euint16 lhs, euint16 rhs) internal pure returns (euint16) {
        if (!isInitialized(lhs)) {
            lhs = asEuint16(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint16(0);
        }
        uint256 unwrappedInput1 = euint16.unwrap(lhs);
        uint256 unwrappedInput2 = euint16.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT16_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).sub);
        return euint16.wrap(result);
    }
    /// @notice This functions performs the sub operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function sub(euint32 lhs, euint32 rhs) internal pure returns (euint32) {
        if (!isInitialized(lhs)) {
            lhs = asEuint32(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint32(0);
        }
        uint256 unwrappedInput1 = euint32.unwrap(lhs);
        uint256 unwrappedInput2 = euint32.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT32_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).sub);
        return euint32.wrap(result);
    }
    /// @notice This functions performs the sub operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function sub(euint64 lhs, euint64 rhs) internal pure returns (euint64) {
        if (!isInitialized(lhs)) {
            lhs = asEuint64(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint64(0);
        }
        uint256 unwrappedInput1 = euint64.unwrap(lhs);
        uint256 unwrappedInput2 = euint64.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT64_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).sub);
        return euint64.wrap(result);
    }
    /// @notice This functions performs the sub operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function sub(euint128 lhs, euint128 rhs) internal pure returns (euint128) {
        if (!isInitialized(lhs)) {
            lhs = asEuint128(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint128(0);
        }
        uint256 unwrappedInput1 = euint128.unwrap(lhs);
        uint256 unwrappedInput2 = euint128.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT128_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).sub);
        return euint128.wrap(result);
    }
    /// @notice This functions performs the mul operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function mul(euint8 lhs, euint8 rhs) internal pure returns (euint8) {
        if (!isInitialized(lhs)) {
            lhs = asEuint8(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint8(0);
        }
        uint256 unwrappedInput1 = euint8.unwrap(lhs);
        uint256 unwrappedInput2 = euint8.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT8_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).mul);
        return euint8.wrap(result);
    }
    /// @notice This functions performs the mul operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function mul(euint16 lhs, euint16 rhs) internal pure returns (euint16) {
        if (!isInitialized(lhs)) {
            lhs = asEuint16(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint16(0);
        }
        uint256 unwrappedInput1 = euint16.unwrap(lhs);
        uint256 unwrappedInput2 = euint16.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT16_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).mul);
        return euint16.wrap(result);
    }
    /// @notice This functions performs the mul operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function mul(euint32 lhs, euint32 rhs) internal pure returns (euint32) {
        if (!isInitialized(lhs)) {
            lhs = asEuint32(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint32(0);
        }
        uint256 unwrappedInput1 = euint32.unwrap(lhs);
        uint256 unwrappedInput2 = euint32.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT32_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).mul);
        return euint32.wrap(result);
    }
    /// @notice This functions performs the mul operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function mul(euint64 lhs, euint64 rhs) internal pure returns (euint64) {
        if (!isInitialized(lhs)) {
            lhs = asEuint64(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint64(0);
        }
        uint256 unwrappedInput1 = euint64.unwrap(lhs);
        uint256 unwrappedInput2 = euint64.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT64_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).mul);
        return euint64.wrap(result);
    }
    /// @notice This functions performs the lt operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function lt(euint8 lhs, euint8 rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEuint8(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint8(0);
        }
        uint256 unwrappedInput1 = euint8.unwrap(lhs);
        uint256 unwrappedInput2 = euint8.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT8_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).lt);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the lt operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function lt(euint16 lhs, euint16 rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEuint16(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint16(0);
        }
        uint256 unwrappedInput1 = euint16.unwrap(lhs);
        uint256 unwrappedInput2 = euint16.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT16_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).lt);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the lt operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function lt(euint32 lhs, euint32 rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEuint32(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint32(0);
        }
        uint256 unwrappedInput1 = euint32.unwrap(lhs);
        uint256 unwrappedInput2 = euint32.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT32_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).lt);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the lt operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function lt(euint64 lhs, euint64 rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEuint64(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint64(0);
        }
        uint256 unwrappedInput1 = euint64.unwrap(lhs);
        uint256 unwrappedInput2 = euint64.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT64_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).lt);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the lt operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function lt(euint128 lhs, euint128 rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEuint128(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint128(0);
        }
        uint256 unwrappedInput1 = euint128.unwrap(lhs);
        uint256 unwrappedInput2 = euint128.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT128_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).lt);
        return ebool.wrap(result);
    }

    function select(ebool input1, ebool input2, ebool input3) internal pure returns (ebool) {
        if (!isInitialized(input1)) {
            input1 = asEbool(0);
        }
        if (!isInitialized(input2)) {
            input2 = asEbool(0);
        }
        if (!isInitialized(input3)) {
            input3 = asEbool(0);
        }

        uint256 unwrappedInput1 = ebool.unwrap(input1);
        uint256 unwrappedInput2 = ebool.unwrap(input2);
        uint256 unwrappedInput3 = ebool.unwrap(input3);

        uint256 result = Impl.select(Common.EBOOL_TFHE, unwrappedInput1, unwrappedInput2, unwrappedInput3);
        return ebool.wrap(result);
    }

    function select(ebool input1, euint8 input2, euint8 input3) internal pure returns (euint8) {
        if (!isInitialized(input1)) {
            input1 = asEbool(0);
        }
        if (!isInitialized(input2)) {
            input2 = asEuint8(0);
        }
        if (!isInitialized(input3)) {
            input3 = asEuint8(0);
        }

        uint256 unwrappedInput1 = ebool.unwrap(input1);
        uint256 unwrappedInput2 = euint8.unwrap(input2);
        uint256 unwrappedInput3 = euint8.unwrap(input3);

        uint256 result = Impl.select(Common.EUINT8_TFHE, unwrappedInput1, unwrappedInput2, unwrappedInput3);
        return euint8.wrap(result);
    }

    function select(ebool input1, euint16 input2, euint16 input3) internal pure returns (euint16) {
        if (!isInitialized(input1)) {
            input1 = asEbool(0);
        }
        if (!isInitialized(input2)) {
            input2 = asEuint16(0);
        }
        if (!isInitialized(input3)) {
            input3 = asEuint16(0);
        }

        uint256 unwrappedInput1 = ebool.unwrap(input1);
        uint256 unwrappedInput2 = euint16.unwrap(input2);
        uint256 unwrappedInput3 = euint16.unwrap(input3);

        uint256 result = Impl.select(Common.EUINT16_TFHE, unwrappedInput1, unwrappedInput2, unwrappedInput3);
        return euint16.wrap(result);
    }

    function select(ebool input1, euint32 input2, euint32 input3) internal pure returns (euint32) {
        if (!isInitialized(input1)) {
            input1 = asEbool(0);
        }
        if (!isInitialized(input2)) {
            input2 = asEuint32(0);
        }
        if (!isInitialized(input3)) {
            input3 = asEuint32(0);
        }

        uint256 unwrappedInput1 = ebool.unwrap(input1);
        uint256 unwrappedInput2 = euint32.unwrap(input2);
        uint256 unwrappedInput3 = euint32.unwrap(input3);

        uint256 result = Impl.select(Common.EUINT32_TFHE, unwrappedInput1, unwrappedInput2, unwrappedInput3);
        return euint32.wrap(result);
    }

    function select(ebool input1, euint64 input2, euint64 input3) internal pure returns (euint64) {
        if (!isInitialized(input1)) {
            input1 = asEbool(0);
        }
        if (!isInitialized(input2)) {
            input2 = asEuint64(0);
        }
        if (!isInitialized(input3)) {
            input3 = asEuint64(0);
        }

        uint256 unwrappedInput1 = ebool.unwrap(input1);
        uint256 unwrappedInput2 = euint64.unwrap(input2);
        uint256 unwrappedInput3 = euint64.unwrap(input3);

        uint256 result = Impl.select(Common.EUINT64_TFHE, unwrappedInput1, unwrappedInput2, unwrappedInput3);
        return euint64.wrap(result);
    }

    function select(ebool input1, euint128 input2, euint128 input3) internal pure returns (euint128) {
        if (!isInitialized(input1)) {
            input1 = asEbool(0);
        }
        if (!isInitialized(input2)) {
            input2 = asEuint128(0);
        }
        if (!isInitialized(input3)) {
            input3 = asEuint128(0);
        }

        uint256 unwrappedInput1 = ebool.unwrap(input1);
        uint256 unwrappedInput2 = euint128.unwrap(input2);
        uint256 unwrappedInput3 = euint128.unwrap(input3);

        uint256 result = Impl.select(Common.EUINT128_TFHE, unwrappedInput1, unwrappedInput2, unwrappedInput3);
        return euint128.wrap(result);
    }

    function select(ebool input1, euint256 input2, euint256 input3) internal pure returns (euint256) {
        if (!isInitialized(input1)) {
            input1 = asEbool(0);
        }
        if (!isInitialized(input2)) {
            input2 = asEuint256(0);
        }
        if (!isInitialized(input3)) {
            input3 = asEuint256(0);
        }

        uint256 unwrappedInput1 = ebool.unwrap(input1);
        uint256 unwrappedInput2 = euint256.unwrap(input2);
        uint256 unwrappedInput3 = euint256.unwrap(input3);

        uint256 result = Impl.select(Common.EUINT256_TFHE, unwrappedInput1, unwrappedInput2, unwrappedInput3);
        return euint256.wrap(result);
    }

    function select(ebool input1, eaddress input2, eaddress input3) internal pure returns (eaddress) {
        if (!isInitialized(input1)) {
            input1 = asEbool(0);
        }
        if (!isInitialized(input2)) {
            input2 = asEaddress(0);
        }
        if (!isInitialized(input3)) {
            input3 = asEaddress(0);
        }

        uint256 unwrappedInput1 = ebool.unwrap(input1);
        uint256 unwrappedInput2 = eaddress.unwrap(input2);
        uint256 unwrappedInput3 = eaddress.unwrap(input3);

        uint256 result = Impl.select(Common.EADDRESS_TFHE, unwrappedInput1, unwrappedInput2, unwrappedInput3);
        return eaddress.wrap(result);
    }
    /// @notice Performs the req operation on a ciphertext
    /// @dev Verifies that the input value matches a valid ciphertext. Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param input1 the input ciphertext
    function req(ebool input1) internal pure  {
        if (!isInitialized(input1)) {
            input1 = asEbool(0);
        }
        uint256 unwrappedInput1 = ebool.unwrap(input1);
        bytes memory inputAsBytes = Common.toBytes(unwrappedInput1);
        FheOps(Precompiles.Fheos).req(Common.EBOOL_TFHE, inputAsBytes);
    }
    /// @notice Performs the req operation on a ciphertext
    /// @dev Verifies that the input value matches a valid ciphertext. Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param input1 the input ciphertext
    function req(euint8 input1) internal pure  {
        if (!isInitialized(input1)) {
            input1 = asEuint8(0);
        }
        uint256 unwrappedInput1 = euint8.unwrap(input1);
        bytes memory inputAsBytes = Common.toBytes(unwrappedInput1);
        FheOps(Precompiles.Fheos).req(Common.EUINT8_TFHE, inputAsBytes);
    }
    /// @notice Performs the req operation on a ciphertext
    /// @dev Verifies that the input value matches a valid ciphertext. Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param input1 the input ciphertext
    function req(euint16 input1) internal pure  {
        if (!isInitialized(input1)) {
            input1 = asEuint16(0);
        }
        uint256 unwrappedInput1 = euint16.unwrap(input1);
        bytes memory inputAsBytes = Common.toBytes(unwrappedInput1);
        FheOps(Precompiles.Fheos).req(Common.EUINT16_TFHE, inputAsBytes);
    }
    /// @notice Performs the req operation on a ciphertext
    /// @dev Verifies that the input value matches a valid ciphertext. Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param input1 the input ciphertext
    function req(euint32 input1) internal pure  {
        if (!isInitialized(input1)) {
            input1 = asEuint32(0);
        }
        uint256 unwrappedInput1 = euint32.unwrap(input1);
        bytes memory inputAsBytes = Common.toBytes(unwrappedInput1);
        FheOps(Precompiles.Fheos).req(Common.EUINT32_TFHE, inputAsBytes);
    }
    /// @notice Performs the req operation on a ciphertext
    /// @dev Verifies that the input value matches a valid ciphertext. Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param input1 the input ciphertext
    function req(euint64 input1) internal pure  {
        if (!isInitialized(input1)) {
            input1 = asEuint64(0);
        }
        uint256 unwrappedInput1 = euint64.unwrap(input1);
        bytes memory inputAsBytes = Common.toBytes(unwrappedInput1);
        FheOps(Precompiles.Fheos).req(Common.EUINT64_TFHE, inputAsBytes);
    }
    /// @notice Performs the req operation on a ciphertext
    /// @dev Verifies that the input value matches a valid ciphertext. Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param input1 the input ciphertext
    function req(euint128 input1) internal pure  {
        if (!isInitialized(input1)) {
            input1 = asEuint128(0);
        }
        uint256 unwrappedInput1 = euint128.unwrap(input1);
        bytes memory inputAsBytes = Common.toBytes(unwrappedInput1);
        FheOps(Precompiles.Fheos).req(Common.EUINT128_TFHE, inputAsBytes);
    }
    /// @notice Performs the req operation on a ciphertext
    /// @dev Verifies that the input value matches a valid ciphertext. Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param input1 the input ciphertext
    function req(euint256 input1) internal pure  {
        if (!isInitialized(input1)) {
            input1 = asEuint256(0);
        }
        uint256 unwrappedInput1 = euint256.unwrap(input1);
        bytes memory inputAsBytes = Common.toBytes(unwrappedInput1);
        FheOps(Precompiles.Fheos).req(Common.EUINT256_TFHE, inputAsBytes);
    }
    /// @notice This functions performs the div operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function div(euint8 lhs, euint8 rhs) internal pure returns (euint8) {
        if (!isInitialized(lhs)) {
            lhs = asEuint8(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint8(0);
        }
        uint256 unwrappedInput1 = euint8.unwrap(lhs);
        uint256 unwrappedInput2 = euint8.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT8_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).div);
        return euint8.wrap(result);
    }
    /// @notice This functions performs the div operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function div(euint16 lhs, euint16 rhs) internal pure returns (euint16) {
        if (!isInitialized(lhs)) {
            lhs = asEuint16(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint16(0);
        }
        uint256 unwrappedInput1 = euint16.unwrap(lhs);
        uint256 unwrappedInput2 = euint16.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT16_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).div);
        return euint16.wrap(result);
    }
    /// @notice This functions performs the div operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function div(euint32 lhs, euint32 rhs) internal pure returns (euint32) {
        if (!isInitialized(lhs)) {
            lhs = asEuint32(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint32(0);
        }
        uint256 unwrappedInput1 = euint32.unwrap(lhs);
        uint256 unwrappedInput2 = euint32.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT32_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).div);
        return euint32.wrap(result);
    }
    /// @notice This functions performs the gt operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function gt(euint8 lhs, euint8 rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEuint8(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint8(0);
        }
        uint256 unwrappedInput1 = euint8.unwrap(lhs);
        uint256 unwrappedInput2 = euint8.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT8_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).gt);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the gt operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function gt(euint16 lhs, euint16 rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEuint16(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint16(0);
        }
        uint256 unwrappedInput1 = euint16.unwrap(lhs);
        uint256 unwrappedInput2 = euint16.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT16_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).gt);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the gt operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function gt(euint32 lhs, euint32 rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEuint32(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint32(0);
        }
        uint256 unwrappedInput1 = euint32.unwrap(lhs);
        uint256 unwrappedInput2 = euint32.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT32_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).gt);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the gt operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function gt(euint64 lhs, euint64 rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEuint64(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint64(0);
        }
        uint256 unwrappedInput1 = euint64.unwrap(lhs);
        uint256 unwrappedInput2 = euint64.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT64_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).gt);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the gt operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function gt(euint128 lhs, euint128 rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEuint128(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint128(0);
        }
        uint256 unwrappedInput1 = euint128.unwrap(lhs);
        uint256 unwrappedInput2 = euint128.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT128_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).gt);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the gte operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function gte(euint8 lhs, euint8 rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEuint8(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint8(0);
        }
        uint256 unwrappedInput1 = euint8.unwrap(lhs);
        uint256 unwrappedInput2 = euint8.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT8_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).gte);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the gte operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function gte(euint16 lhs, euint16 rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEuint16(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint16(0);
        }
        uint256 unwrappedInput1 = euint16.unwrap(lhs);
        uint256 unwrappedInput2 = euint16.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT16_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).gte);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the gte operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function gte(euint32 lhs, euint32 rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEuint32(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint32(0);
        }
        uint256 unwrappedInput1 = euint32.unwrap(lhs);
        uint256 unwrappedInput2 = euint32.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT32_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).gte);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the gte operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function gte(euint64 lhs, euint64 rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEuint64(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint64(0);
        }
        uint256 unwrappedInput1 = euint64.unwrap(lhs);
        uint256 unwrappedInput2 = euint64.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT64_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).gte);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the gte operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function gte(euint128 lhs, euint128 rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEuint128(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint128(0);
        }
        uint256 unwrappedInput1 = euint128.unwrap(lhs);
        uint256 unwrappedInput2 = euint128.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT128_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).gte);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the rem operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function rem(euint8 lhs, euint8 rhs) internal pure returns (euint8) {
        if (!isInitialized(lhs)) {
            lhs = asEuint8(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint8(0);
        }
        uint256 unwrappedInput1 = euint8.unwrap(lhs);
        uint256 unwrappedInput2 = euint8.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT8_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).rem);
        return euint8.wrap(result);
    }
    /// @notice This functions performs the rem operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function rem(euint16 lhs, euint16 rhs) internal pure returns (euint16) {
        if (!isInitialized(lhs)) {
            lhs = asEuint16(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint16(0);
        }
        uint256 unwrappedInput1 = euint16.unwrap(lhs);
        uint256 unwrappedInput2 = euint16.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT16_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).rem);
        return euint16.wrap(result);
    }
    /// @notice This functions performs the rem operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function rem(euint32 lhs, euint32 rhs) internal pure returns (euint32) {
        if (!isInitialized(lhs)) {
            lhs = asEuint32(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint32(0);
        }
        uint256 unwrappedInput1 = euint32.unwrap(lhs);
        uint256 unwrappedInput2 = euint32.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT32_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).rem);
        return euint32.wrap(result);
    }
    /// @notice This functions performs the and operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function and(ebool lhs, ebool rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEbool(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEbool(0);
        }
        uint256 unwrappedInput1 = ebool.unwrap(lhs);
        uint256 unwrappedInput2 = ebool.unwrap(rhs);

        uint256 result = mathHelper(Common.EBOOL_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).and);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the and operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function and(euint8 lhs, euint8 rhs) internal pure returns (euint8) {
        if (!isInitialized(lhs)) {
            lhs = asEuint8(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint8(0);
        }
        uint256 unwrappedInput1 = euint8.unwrap(lhs);
        uint256 unwrappedInput2 = euint8.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT8_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).and);
        return euint8.wrap(result);
    }
    /// @notice This functions performs the and operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function and(euint16 lhs, euint16 rhs) internal pure returns (euint16) {
        if (!isInitialized(lhs)) {
            lhs = asEuint16(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint16(0);
        }
        uint256 unwrappedInput1 = euint16.unwrap(lhs);
        uint256 unwrappedInput2 = euint16.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT16_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).and);
        return euint16.wrap(result);
    }
    /// @notice This functions performs the and operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function and(euint32 lhs, euint32 rhs) internal pure returns (euint32) {
        if (!isInitialized(lhs)) {
            lhs = asEuint32(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint32(0);
        }
        uint256 unwrappedInput1 = euint32.unwrap(lhs);
        uint256 unwrappedInput2 = euint32.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT32_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).and);
        return euint32.wrap(result);
    }
    /// @notice This functions performs the and operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function and(euint64 lhs, euint64 rhs) internal pure returns (euint64) {
        if (!isInitialized(lhs)) {
            lhs = asEuint64(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint64(0);
        }
        uint256 unwrappedInput1 = euint64.unwrap(lhs);
        uint256 unwrappedInput2 = euint64.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT64_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).and);
        return euint64.wrap(result);
    }
    /// @notice This functions performs the and operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function and(euint128 lhs, euint128 rhs) internal pure returns (euint128) {
        if (!isInitialized(lhs)) {
            lhs = asEuint128(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint128(0);
        }
        uint256 unwrappedInput1 = euint128.unwrap(lhs);
        uint256 unwrappedInput2 = euint128.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT128_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).and);
        return euint128.wrap(result);
    }
    /// @notice This functions performs the or operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function or(ebool lhs, ebool rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEbool(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEbool(0);
        }
        uint256 unwrappedInput1 = ebool.unwrap(lhs);
        uint256 unwrappedInput2 = ebool.unwrap(rhs);

        uint256 result = mathHelper(Common.EBOOL_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).or);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the or operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function or(euint8 lhs, euint8 rhs) internal pure returns (euint8) {
        if (!isInitialized(lhs)) {
            lhs = asEuint8(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint8(0);
        }
        uint256 unwrappedInput1 = euint8.unwrap(lhs);
        uint256 unwrappedInput2 = euint8.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT8_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).or);
        return euint8.wrap(result);
    }
    /// @notice This functions performs the or operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function or(euint16 lhs, euint16 rhs) internal pure returns (euint16) {
        if (!isInitialized(lhs)) {
            lhs = asEuint16(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint16(0);
        }
        uint256 unwrappedInput1 = euint16.unwrap(lhs);
        uint256 unwrappedInput2 = euint16.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT16_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).or);
        return euint16.wrap(result);
    }
    /// @notice This functions performs the or operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function or(euint32 lhs, euint32 rhs) internal pure returns (euint32) {
        if (!isInitialized(lhs)) {
            lhs = asEuint32(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint32(0);
        }
        uint256 unwrappedInput1 = euint32.unwrap(lhs);
        uint256 unwrappedInput2 = euint32.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT32_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).or);
        return euint32.wrap(result);
    }
    /// @notice This functions performs the or operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function or(euint64 lhs, euint64 rhs) internal pure returns (euint64) {
        if (!isInitialized(lhs)) {
            lhs = asEuint64(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint64(0);
        }
        uint256 unwrappedInput1 = euint64.unwrap(lhs);
        uint256 unwrappedInput2 = euint64.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT64_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).or);
        return euint64.wrap(result);
    }
    /// @notice This functions performs the or operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function or(euint128 lhs, euint128 rhs) internal pure returns (euint128) {
        if (!isInitialized(lhs)) {
            lhs = asEuint128(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint128(0);
        }
        uint256 unwrappedInput1 = euint128.unwrap(lhs);
        uint256 unwrappedInput2 = euint128.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT128_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).or);
        return euint128.wrap(result);
    }
    /// @notice This functions performs the xor operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function xor(ebool lhs, ebool rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEbool(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEbool(0);
        }
        uint256 unwrappedInput1 = ebool.unwrap(lhs);
        uint256 unwrappedInput2 = ebool.unwrap(rhs);

        uint256 result = mathHelper(Common.EBOOL_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).xor);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the xor operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function xor(euint8 lhs, euint8 rhs) internal pure returns (euint8) {
        if (!isInitialized(lhs)) {
            lhs = asEuint8(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint8(0);
        }
        uint256 unwrappedInput1 = euint8.unwrap(lhs);
        uint256 unwrappedInput2 = euint8.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT8_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).xor);
        return euint8.wrap(result);
    }
    /// @notice This functions performs the xor operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function xor(euint16 lhs, euint16 rhs) internal pure returns (euint16) {
        if (!isInitialized(lhs)) {
            lhs = asEuint16(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint16(0);
        }
        uint256 unwrappedInput1 = euint16.unwrap(lhs);
        uint256 unwrappedInput2 = euint16.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT16_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).xor);
        return euint16.wrap(result);
    }
    /// @notice This functions performs the xor operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function xor(euint32 lhs, euint32 rhs) internal pure returns (euint32) {
        if (!isInitialized(lhs)) {
            lhs = asEuint32(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint32(0);
        }
        uint256 unwrappedInput1 = euint32.unwrap(lhs);
        uint256 unwrappedInput2 = euint32.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT32_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).xor);
        return euint32.wrap(result);
    }
    /// @notice This functions performs the xor operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function xor(euint64 lhs, euint64 rhs) internal pure returns (euint64) {
        if (!isInitialized(lhs)) {
            lhs = asEuint64(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint64(0);
        }
        uint256 unwrappedInput1 = euint64.unwrap(lhs);
        uint256 unwrappedInput2 = euint64.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT64_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).xor);
        return euint64.wrap(result);
    }
    /// @notice This functions performs the xor operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function xor(euint128 lhs, euint128 rhs) internal pure returns (euint128) {
        if (!isInitialized(lhs)) {
            lhs = asEuint128(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint128(0);
        }
        uint256 unwrappedInput1 = euint128.unwrap(lhs);
        uint256 unwrappedInput2 = euint128.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT128_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).xor);
        return euint128.wrap(result);
    }
    /// @notice This functions performs the eq operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function eq(ebool lhs, ebool rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEbool(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEbool(0);
        }
        uint256 unwrappedInput1 = ebool.unwrap(lhs);
        uint256 unwrappedInput2 = ebool.unwrap(rhs);

        uint256 result = mathHelper(Common.EBOOL_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).eq);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the eq operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function eq(euint8 lhs, euint8 rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEuint8(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint8(0);
        }
        uint256 unwrappedInput1 = euint8.unwrap(lhs);
        uint256 unwrappedInput2 = euint8.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT8_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).eq);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the eq operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function eq(euint16 lhs, euint16 rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEuint16(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint16(0);
        }
        uint256 unwrappedInput1 = euint16.unwrap(lhs);
        uint256 unwrappedInput2 = euint16.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT16_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).eq);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the eq operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function eq(euint32 lhs, euint32 rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEuint32(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint32(0);
        }
        uint256 unwrappedInput1 = euint32.unwrap(lhs);
        uint256 unwrappedInput2 = euint32.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT32_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).eq);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the eq operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function eq(euint64 lhs, euint64 rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEuint64(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint64(0);
        }
        uint256 unwrappedInput1 = euint64.unwrap(lhs);
        uint256 unwrappedInput2 = euint64.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT64_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).eq);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the eq operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function eq(euint128 lhs, euint128 rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEuint128(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint128(0);
        }
        uint256 unwrappedInput1 = euint128.unwrap(lhs);
        uint256 unwrappedInput2 = euint128.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT128_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).eq);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the eq operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function eq(euint256 lhs, euint256 rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEuint256(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint256(0);
        }
        uint256 unwrappedInput1 = euint256.unwrap(lhs);
        uint256 unwrappedInput2 = euint256.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT256_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).eq);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the eq operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function eq(eaddress lhs, eaddress rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEaddress(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEaddress(0);
        }
        uint256 unwrappedInput1 = eaddress.unwrap(lhs);
        uint256 unwrappedInput2 = eaddress.unwrap(rhs);

        uint256 result = mathHelper(Common.EADDRESS_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).eq);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the ne operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function ne(ebool lhs, ebool rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEbool(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEbool(0);
        }
        uint256 unwrappedInput1 = ebool.unwrap(lhs);
        uint256 unwrappedInput2 = ebool.unwrap(rhs);

        uint256 result = mathHelper(Common.EBOOL_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).ne);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the ne operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function ne(euint8 lhs, euint8 rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEuint8(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint8(0);
        }
        uint256 unwrappedInput1 = euint8.unwrap(lhs);
        uint256 unwrappedInput2 = euint8.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT8_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).ne);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the ne operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function ne(euint16 lhs, euint16 rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEuint16(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint16(0);
        }
        uint256 unwrappedInput1 = euint16.unwrap(lhs);
        uint256 unwrappedInput2 = euint16.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT16_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).ne);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the ne operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function ne(euint32 lhs, euint32 rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEuint32(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint32(0);
        }
        uint256 unwrappedInput1 = euint32.unwrap(lhs);
        uint256 unwrappedInput2 = euint32.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT32_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).ne);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the ne operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function ne(euint64 lhs, euint64 rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEuint64(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint64(0);
        }
        uint256 unwrappedInput1 = euint64.unwrap(lhs);
        uint256 unwrappedInput2 = euint64.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT64_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).ne);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the ne operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function ne(euint128 lhs, euint128 rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEuint128(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint128(0);
        }
        uint256 unwrappedInput1 = euint128.unwrap(lhs);
        uint256 unwrappedInput2 = euint128.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT128_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).ne);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the ne operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function ne(euint256 lhs, euint256 rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEuint256(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint256(0);
        }
        uint256 unwrappedInput1 = euint256.unwrap(lhs);
        uint256 unwrappedInput2 = euint256.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT256_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).ne);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the ne operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function ne(eaddress lhs, eaddress rhs) internal pure returns (ebool) {
        if (!isInitialized(lhs)) {
            lhs = asEaddress(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEaddress(0);
        }
        uint256 unwrappedInput1 = eaddress.unwrap(lhs);
        uint256 unwrappedInput2 = eaddress.unwrap(rhs);

        uint256 result = mathHelper(Common.EADDRESS_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).ne);
        return ebool.wrap(result);
    }
    /// @notice This functions performs the min operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function min(euint8 lhs, euint8 rhs) internal pure returns (euint8) {
        if (!isInitialized(lhs)) {
            lhs = asEuint8(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint8(0);
        }
        uint256 unwrappedInput1 = euint8.unwrap(lhs);
        uint256 unwrappedInput2 = euint8.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT8_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).min);
        return euint8.wrap(result);
    }
    /// @notice This functions performs the min operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function min(euint16 lhs, euint16 rhs) internal pure returns (euint16) {
        if (!isInitialized(lhs)) {
            lhs = asEuint16(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint16(0);
        }
        uint256 unwrappedInput1 = euint16.unwrap(lhs);
        uint256 unwrappedInput2 = euint16.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT16_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).min);
        return euint16.wrap(result);
    }
    /// @notice This functions performs the min operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function min(euint32 lhs, euint32 rhs) internal pure returns (euint32) {
        if (!isInitialized(lhs)) {
            lhs = asEuint32(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint32(0);
        }
        uint256 unwrappedInput1 = euint32.unwrap(lhs);
        uint256 unwrappedInput2 = euint32.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT32_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).min);
        return euint32.wrap(result);
    }
    /// @notice This functions performs the min operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function min(euint64 lhs, euint64 rhs) internal pure returns (euint64) {
        if (!isInitialized(lhs)) {
            lhs = asEuint64(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint64(0);
        }
        uint256 unwrappedInput1 = euint64.unwrap(lhs);
        uint256 unwrappedInput2 = euint64.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT64_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).min);
        return euint64.wrap(result);
    }
    /// @notice This functions performs the min operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function min(euint128 lhs, euint128 rhs) internal pure returns (euint128) {
        if (!isInitialized(lhs)) {
            lhs = asEuint128(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint128(0);
        }
        uint256 unwrappedInput1 = euint128.unwrap(lhs);
        uint256 unwrappedInput2 = euint128.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT128_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).min);
        return euint128.wrap(result);
    }
    /// @notice This functions performs the max operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function max(euint8 lhs, euint8 rhs) internal pure returns (euint8) {
        if (!isInitialized(lhs)) {
            lhs = asEuint8(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint8(0);
        }
        uint256 unwrappedInput1 = euint8.unwrap(lhs);
        uint256 unwrappedInput2 = euint8.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT8_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).max);
        return euint8.wrap(result);
    }
    /// @notice This functions performs the max operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function max(euint16 lhs, euint16 rhs) internal pure returns (euint16) {
        if (!isInitialized(lhs)) {
            lhs = asEuint16(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint16(0);
        }
        uint256 unwrappedInput1 = euint16.unwrap(lhs);
        uint256 unwrappedInput2 = euint16.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT16_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).max);
        return euint16.wrap(result);
    }
    /// @notice This functions performs the max operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function max(euint32 lhs, euint32 rhs) internal pure returns (euint32) {
        if (!isInitialized(lhs)) {
            lhs = asEuint32(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint32(0);
        }
        uint256 unwrappedInput1 = euint32.unwrap(lhs);
        uint256 unwrappedInput2 = euint32.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT32_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).max);
        return euint32.wrap(result);
    }
    /// @notice This functions performs the max operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function max(euint64 lhs, euint64 rhs) internal pure returns (euint64) {
        if (!isInitialized(lhs)) {
            lhs = asEuint64(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint64(0);
        }
        uint256 unwrappedInput1 = euint64.unwrap(lhs);
        uint256 unwrappedInput2 = euint64.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT64_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).max);
        return euint64.wrap(result);
    }
    /// @notice This functions performs the max operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function max(euint128 lhs, euint128 rhs) internal pure returns (euint128) {
        if (!isInitialized(lhs)) {
            lhs = asEuint128(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint128(0);
        }
        uint256 unwrappedInput1 = euint128.unwrap(lhs);
        uint256 unwrappedInput2 = euint128.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT128_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).max);
        return euint128.wrap(result);
    }
    /// @notice This functions performs the shl operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function shl(euint8 lhs, euint8 rhs) internal pure returns (euint8) {
        if (!isInitialized(lhs)) {
            lhs = asEuint8(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint8(0);
        }
        uint256 unwrappedInput1 = euint8.unwrap(lhs);
        uint256 unwrappedInput2 = euint8.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT8_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).shl);
        return euint8.wrap(result);
    }
    /// @notice This functions performs the shl operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function shl(euint16 lhs, euint16 rhs) internal pure returns (euint16) {
        if (!isInitialized(lhs)) {
            lhs = asEuint16(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint16(0);
        }
        uint256 unwrappedInput1 = euint16.unwrap(lhs);
        uint256 unwrappedInput2 = euint16.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT16_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).shl);
        return euint16.wrap(result);
    }
    /// @notice This functions performs the shl operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function shl(euint32 lhs, euint32 rhs) internal pure returns (euint32) {
        if (!isInitialized(lhs)) {
            lhs = asEuint32(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint32(0);
        }
        uint256 unwrappedInput1 = euint32.unwrap(lhs);
        uint256 unwrappedInput2 = euint32.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT32_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).shl);
        return euint32.wrap(result);
    }
    /// @notice This functions performs the shl operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function shl(euint64 lhs, euint64 rhs) internal pure returns (euint64) {
        if (!isInitialized(lhs)) {
            lhs = asEuint64(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint64(0);
        }
        uint256 unwrappedInput1 = euint64.unwrap(lhs);
        uint256 unwrappedInput2 = euint64.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT64_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).shl);
        return euint64.wrap(result);
    }
    /// @notice This functions performs the shl operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function shl(euint128 lhs, euint128 rhs) internal pure returns (euint128) {
        if (!isInitialized(lhs)) {
            lhs = asEuint128(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint128(0);
        }
        uint256 unwrappedInput1 = euint128.unwrap(lhs);
        uint256 unwrappedInput2 = euint128.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT128_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).shl);
        return euint128.wrap(result);
    }
    /// @notice This functions performs the shr operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function shr(euint8 lhs, euint8 rhs) internal pure returns (euint8) {
        if (!isInitialized(lhs)) {
            lhs = asEuint8(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint8(0);
        }
        uint256 unwrappedInput1 = euint8.unwrap(lhs);
        uint256 unwrappedInput2 = euint8.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT8_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).shr);
        return euint8.wrap(result);
    }
    /// @notice This functions performs the shr operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function shr(euint16 lhs, euint16 rhs) internal pure returns (euint16) {
        if (!isInitialized(lhs)) {
            lhs = asEuint16(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint16(0);
        }
        uint256 unwrappedInput1 = euint16.unwrap(lhs);
        uint256 unwrappedInput2 = euint16.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT16_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).shr);
        return euint16.wrap(result);
    }
    /// @notice This functions performs the shr operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function shr(euint32 lhs, euint32 rhs) internal pure returns (euint32) {
        if (!isInitialized(lhs)) {
            lhs = asEuint32(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint32(0);
        }
        uint256 unwrappedInput1 = euint32.unwrap(lhs);
        uint256 unwrappedInput2 = euint32.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT32_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).shr);
        return euint32.wrap(result);
    }
    /// @notice This functions performs the shr operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function shr(euint64 lhs, euint64 rhs) internal pure returns (euint64) {
        if (!isInitialized(lhs)) {
            lhs = asEuint64(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint64(0);
        }
        uint256 unwrappedInput1 = euint64.unwrap(lhs);
        uint256 unwrappedInput2 = euint64.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT64_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).shr);
        return euint64.wrap(result);
    }
    /// @notice This functions performs the shr operation
    /// @dev If any of the inputs are expected to be a ciphertext, it verifies that the value matches a valid ciphertext
    ///Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs The first input 
    /// @param rhs The second input
    /// @return The result of the operation
    function shr(euint128 lhs, euint128 rhs) internal pure returns (euint128) {
        if (!isInitialized(lhs)) {
            lhs = asEuint128(0);
        }
        if (!isInitialized(rhs)) {
            rhs = asEuint128(0);
        }
        uint256 unwrappedInput1 = euint128.unwrap(lhs);
        uint256 unwrappedInput2 = euint128.unwrap(rhs);

        uint256 result = mathHelper(Common.EUINT128_TFHE, unwrappedInput1, unwrappedInput2, FheOps(Precompiles.Fheos).shr);
        return euint128.wrap(result);
    }

    /// @notice Performs the "not" for the ebool type
    /// @dev Implemented by a workaround due to ebool being a euint8 type behind the scenes, therefore xor is needed to assure that not(true) = false and vise-versa
    /// @param value input ebool ciphertext
    /// @return Result of the not operation on `value` 
    function not(ebool value) internal pure returns (ebool) {
        return xor(value, asEbool(true));
    }
    /// @notice Performs the not operation on a ciphertext
    /// @dev Verifies that the input value matches a valid ciphertext. Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param input1 the input ciphertext
    function not(euint8 input1) internal pure returns (euint8) {
        if (!isInitialized(input1)) {
            input1 = asEuint8(0);
        }
        uint256 unwrappedInput1 = euint8.unwrap(input1);
        bytes memory inputAsBytes = Common.toBytes(unwrappedInput1);
        bytes memory b = FheOps(Precompiles.Fheos).not(Common.EUINT8_TFHE, inputAsBytes);
        uint256 result = Impl.getValue(b);
        return euint8.wrap(result);
    }
    /// @notice Performs the not operation on a ciphertext
    /// @dev Verifies that the input value matches a valid ciphertext. Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param input1 the input ciphertext
    function not(euint16 input1) internal pure returns (euint16) {
        if (!isInitialized(input1)) {
            input1 = asEuint16(0);
        }
        uint256 unwrappedInput1 = euint16.unwrap(input1);
        bytes memory inputAsBytes = Common.toBytes(unwrappedInput1);
        bytes memory b = FheOps(Precompiles.Fheos).not(Common.EUINT16_TFHE, inputAsBytes);
        uint256 result = Impl.getValue(b);
        return euint16.wrap(result);
    }
    /// @notice Performs the not operation on a ciphertext
    /// @dev Verifies that the input value matches a valid ciphertext. Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param input1 the input ciphertext
    function not(euint32 input1) internal pure returns (euint32) {
        if (!isInitialized(input1)) {
            input1 = asEuint32(0);
        }
        uint256 unwrappedInput1 = euint32.unwrap(input1);
        bytes memory inputAsBytes = Common.toBytes(unwrappedInput1);
        bytes memory b = FheOps(Precompiles.Fheos).not(Common.EUINT32_TFHE, inputAsBytes);
        uint256 result = Impl.getValue(b);
        return euint32.wrap(result);
    }
    /// @notice Performs the not operation on a ciphertext
    /// @dev Verifies that the input value matches a valid ciphertext. Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param input1 the input ciphertext
    function not(euint64 input1) internal pure returns (euint64) {
        if (!isInitialized(input1)) {
            input1 = asEuint64(0);
        }
        uint256 unwrappedInput1 = euint64.unwrap(input1);
        bytes memory inputAsBytes = Common.toBytes(unwrappedInput1);
        bytes memory b = FheOps(Precompiles.Fheos).not(Common.EUINT64_TFHE, inputAsBytes);
        uint256 result = Impl.getValue(b);
        return euint64.wrap(result);
    }
    /// @notice Performs the not operation on a ciphertext
    /// @dev Verifies that the input value matches a valid ciphertext. Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param input1 the input ciphertext
    function not(euint128 input1) internal pure returns (euint128) {
        if (!isInitialized(input1)) {
            input1 = asEuint128(0);
        }
        uint256 unwrappedInput1 = euint128.unwrap(input1);
        bytes memory inputAsBytes = Common.toBytes(unwrappedInput1);
        bytes memory b = FheOps(Precompiles.Fheos).not(Common.EUINT128_TFHE, inputAsBytes);
        uint256 result = Impl.getValue(b);
        return euint128.wrap(result);
    }

    // ********** TYPE CASTING ************* //
    /// @notice Parses input ciphertexts from the user. Converts from encrypted raw bytes to an ebool
    /// @dev Also performs validation that the ciphertext is valid and has been encrypted using the network encryption key
    /// @return a ciphertext representation of the input
    function asEbool(inEbool memory value) internal pure returns (ebool) {
        return FHE.asEbool(value.data);
    }
    /// @notice Converts a ebool to an euint8
    function asEuint8(ebool value) internal pure returns (euint8) {
        return euint8.wrap(Impl.cast(Common.EBOOL_TFHE, ebool.unwrap(value), Common.EUINT8_TFHE));
    }
    /// @notice Converts a ebool to an euint16
    function asEuint16(ebool value) internal pure returns (euint16) {
        return euint16.wrap(Impl.cast(Common.EBOOL_TFHE, ebool.unwrap(value), Common.EUINT16_TFHE));
    }
    /// @notice Converts a ebool to an euint32
    function asEuint32(ebool value) internal pure returns (euint32) {
        return euint32.wrap(Impl.cast(Common.EBOOL_TFHE, ebool.unwrap(value), Common.EUINT32_TFHE));
    }
    /// @notice Converts a ebool to an euint64
    function asEuint64(ebool value) internal pure returns (euint64) {
        return euint64.wrap(Impl.cast(Common.EBOOL_TFHE, ebool.unwrap(value), Common.EUINT64_TFHE));
    }
    /// @notice Converts a ebool to an euint128
    function asEuint128(ebool value) internal pure returns (euint128) {
        return euint128.wrap(Impl.cast(Common.EBOOL_TFHE, ebool.unwrap(value), Common.EUINT128_TFHE));
    }
    /// @notice Converts a ebool to an euint256
    function asEuint256(ebool value) internal pure returns (euint256) {
        return euint256.wrap(Impl.cast(Common.EBOOL_TFHE, ebool.unwrap(value), Common.EUINT256_TFHE));
    }
    /// @notice Converts a ebool to an eaddress
    function asEaddress(ebool value) internal pure returns (eaddress) {
        return eaddress.wrap(Impl.cast(Common.EBOOL_TFHE, ebool.unwrap(value), Common.EADDRESS_TFHE));
    }
    
    /// @notice Converts a euint8 to an ebool
    function asEbool(euint8 value) internal pure returns (ebool) {
        return ne(value, asEuint8(0));
    }
    /// @notice Parses input ciphertexts from the user. Converts from encrypted raw bytes to an euint8
    /// @dev Also performs validation that the ciphertext is valid and has been encrypted using the network encryption key
    /// @return a ciphertext representation of the input
    function asEuint8(inEuint8 memory value) internal pure returns (euint8) {
        return FHE.asEuint8(value.data);
    }
    /// @notice Converts a euint8 to an euint16
    function asEuint16(euint8 value) internal pure returns (euint16) {
        return euint16.wrap(Impl.cast(Common.EUINT8_TFHE, euint8.unwrap(value), Common.EUINT16_TFHE));
    }
    /// @notice Converts a euint8 to an euint32
    function asEuint32(euint8 value) internal pure returns (euint32) {
        return euint32.wrap(Impl.cast(Common.EUINT8_TFHE, euint8.unwrap(value), Common.EUINT32_TFHE));
    }
    /// @notice Converts a euint8 to an euint64
    function asEuint64(euint8 value) internal pure returns (euint64) {
        return euint64.wrap(Impl.cast(Common.EUINT8_TFHE, euint8.unwrap(value), Common.EUINT64_TFHE));
    }
    /// @notice Converts a euint8 to an euint128
    function asEuint128(euint8 value) internal pure returns (euint128) {
        return euint128.wrap(Impl.cast(Common.EUINT8_TFHE, euint8.unwrap(value), Common.EUINT128_TFHE));
    }
    /// @notice Converts a euint8 to an euint256
    function asEuint256(euint8 value) internal pure returns (euint256) {
        return euint256.wrap(Impl.cast(Common.EUINT8_TFHE, euint8.unwrap(value), Common.EUINT256_TFHE));
    }
    /// @notice Converts a euint8 to an eaddress
    function asEaddress(euint8 value) internal pure returns (eaddress) {
        return eaddress.wrap(Impl.cast(Common.EUINT8_TFHE, euint8.unwrap(value), Common.EADDRESS_TFHE));
    }
    
    /// @notice Converts a euint16 to an ebool
    function asEbool(euint16 value) internal pure returns (ebool) {
        return ne(value, asEuint16(0));
    }
    /// @notice Converts a euint16 to an euint8
    function asEuint8(euint16 value) internal pure returns (euint8) {
        return euint8.wrap(Impl.cast(Common.EUINT16_TFHE, euint16.unwrap(value), Common.EUINT8_TFHE));
    }
    /// @notice Parses input ciphertexts from the user. Converts from encrypted raw bytes to an euint16
    /// @dev Also performs validation that the ciphertext is valid and has been encrypted using the network encryption key
    /// @return a ciphertext representation of the input
    function asEuint16(inEuint16 memory value) internal pure returns (euint16) {
        return FHE.asEuint16(value.data);
    }
    /// @notice Converts a euint16 to an euint32
    function asEuint32(euint16 value) internal pure returns (euint32) {
        return euint32.wrap(Impl.cast(Common.EUINT16_TFHE, euint16.unwrap(value), Common.EUINT32_TFHE));
    }
    /// @notice Converts a euint16 to an euint64
    function asEuint64(euint16 value) internal pure returns (euint64) {
        return euint64.wrap(Impl.cast(Common.EUINT16_TFHE, euint16.unwrap(value), Common.EUINT64_TFHE));
    }
    /// @notice Converts a euint16 to an euint128
    function asEuint128(euint16 value) internal pure returns (euint128) {
        return euint128.wrap(Impl.cast(Common.EUINT16_TFHE, euint16.unwrap(value), Common.EUINT128_TFHE));
    }
    /// @notice Converts a euint16 to an euint256
    function asEuint256(euint16 value) internal pure returns (euint256) {
        return euint256.wrap(Impl.cast(Common.EUINT16_TFHE, euint16.unwrap(value), Common.EUINT256_TFHE));
    }
    /// @notice Converts a euint16 to an eaddress
    function asEaddress(euint16 value) internal pure returns (eaddress) {
        return eaddress.wrap(Impl.cast(Common.EUINT16_TFHE, euint16.unwrap(value), Common.EADDRESS_TFHE));
    }
    
    /// @notice Converts a euint32 to an ebool
    function asEbool(euint32 value) internal pure returns (ebool) {
        return ne(value, asEuint32(0));
    }
    /// @notice Converts a euint32 to an euint8
    function asEuint8(euint32 value) internal pure returns (euint8) {
        return euint8.wrap(Impl.cast(Common.EUINT32_TFHE, euint32.unwrap(value), Common.EUINT8_TFHE));
    }
    /// @notice Converts a euint32 to an euint16
    function asEuint16(euint32 value) internal pure returns (euint16) {
        return euint16.wrap(Impl.cast(Common.EUINT32_TFHE, euint32.unwrap(value), Common.EUINT16_TFHE));
    }
    /// @notice Parses input ciphertexts from the user. Converts from encrypted raw bytes to an euint32
    /// @dev Also performs validation that the ciphertext is valid and has been encrypted using the network encryption key
    /// @return a ciphertext representation of the input
    function asEuint32(inEuint32 memory value) internal pure returns (euint32) {
        return FHE.asEuint32(value.data);
    }
    /// @notice Converts a euint32 to an euint64
    function asEuint64(euint32 value) internal pure returns (euint64) {
        return euint64.wrap(Impl.cast(Common.EUINT32_TFHE, euint32.unwrap(value), Common.EUINT64_TFHE));
    }
    /// @notice Converts a euint32 to an euint128
    function asEuint128(euint32 value) internal pure returns (euint128) {
        return euint128.wrap(Impl.cast(Common.EUINT32_TFHE, euint32.unwrap(value), Common.EUINT128_TFHE));
    }
    /// @notice Converts a euint32 to an euint256
    function asEuint256(euint32 value) internal pure returns (euint256) {
        return euint256.wrap(Impl.cast(Common.EUINT32_TFHE, euint32.unwrap(value), Common.EUINT256_TFHE));
    }
    /// @notice Converts a euint32 to an eaddress
    function asEaddress(euint32 value) internal pure returns (eaddress) {
        return eaddress.wrap(Impl.cast(Common.EUINT32_TFHE, euint32.unwrap(value), Common.EADDRESS_TFHE));
    }
    
    /// @notice Converts a euint64 to an ebool
    function asEbool(euint64 value) internal pure returns (ebool) {
        return ne(value, asEuint64(0));
    }
    /// @notice Converts a euint64 to an euint8
    function asEuint8(euint64 value) internal pure returns (euint8) {
        return euint8.wrap(Impl.cast(Common.EUINT64_TFHE, euint64.unwrap(value), Common.EUINT8_TFHE));
    }
    /// @notice Converts a euint64 to an euint16
    function asEuint16(euint64 value) internal pure returns (euint16) {
        return euint16.wrap(Impl.cast(Common.EUINT64_TFHE, euint64.unwrap(value), Common.EUINT16_TFHE));
    }
    /// @notice Converts a euint64 to an euint32
    function asEuint32(euint64 value) internal pure returns (euint32) {
        return euint32.wrap(Impl.cast(Common.EUINT64_TFHE, euint64.unwrap(value), Common.EUINT32_TFHE));
    }
    /// @notice Parses input ciphertexts from the user. Converts from encrypted raw bytes to an euint64
    /// @dev Also performs validation that the ciphertext is valid and has been encrypted using the network encryption key
    /// @return a ciphertext representation of the input
    function asEuint64(inEuint64 memory value) internal pure returns (euint64) {
        return FHE.asEuint64(value.data);
    }
    /// @notice Converts a euint64 to an euint128
    function asEuint128(euint64 value) internal pure returns (euint128) {
        return euint128.wrap(Impl.cast(Common.EUINT64_TFHE, euint64.unwrap(value), Common.EUINT128_TFHE));
    }
    /// @notice Converts a euint64 to an euint256
    function asEuint256(euint64 value) internal pure returns (euint256) {
        return euint256.wrap(Impl.cast(Common.EUINT64_TFHE, euint64.unwrap(value), Common.EUINT256_TFHE));
    }
    /// @notice Converts a euint64 to an eaddress
    function asEaddress(euint64 value) internal pure returns (eaddress) {
        return eaddress.wrap(Impl.cast(Common.EUINT64_TFHE, euint64.unwrap(value), Common.EADDRESS_TFHE));
    }
    
    /// @notice Converts a euint128 to an ebool
    function asEbool(euint128 value) internal pure returns (ebool) {
        return ne(value, asEuint128(0));
    }
    /// @notice Converts a euint128 to an euint8
    function asEuint8(euint128 value) internal pure returns (euint8) {
        return euint8.wrap(Impl.cast(Common.EUINT128_TFHE, euint128.unwrap(value), Common.EUINT8_TFHE));
    }
    /// @notice Converts a euint128 to an euint16
    function asEuint16(euint128 value) internal pure returns (euint16) {
        return euint16.wrap(Impl.cast(Common.EUINT128_TFHE, euint128.unwrap(value), Common.EUINT16_TFHE));
    }
    /// @notice Converts a euint128 to an euint32
    function asEuint32(euint128 value) internal pure returns (euint32) {
        return euint32.wrap(Impl.cast(Common.EUINT128_TFHE, euint128.unwrap(value), Common.EUINT32_TFHE));
    }
    /// @notice Converts a euint128 to an euint64
    function asEuint64(euint128 value) internal pure returns (euint64) {
        return euint64.wrap(Impl.cast(Common.EUINT128_TFHE, euint128.unwrap(value), Common.EUINT64_TFHE));
    }
    /// @notice Parses input ciphertexts from the user. Converts from encrypted raw bytes to an euint128
    /// @dev Also performs validation that the ciphertext is valid and has been encrypted using the network encryption key
    /// @return a ciphertext representation of the input
    function asEuint128(inEuint128 memory value) internal pure returns (euint128) {
        return FHE.asEuint128(value.data);
    }
    /// @notice Converts a euint128 to an euint256
    function asEuint256(euint128 value) internal pure returns (euint256) {
        return euint256.wrap(Impl.cast(Common.EUINT128_TFHE, euint128.unwrap(value), Common.EUINT256_TFHE));
    }
    /// @notice Converts a euint128 to an eaddress
    function asEaddress(euint128 value) internal pure returns (eaddress) {
        return eaddress.wrap(Impl.cast(Common.EUINT128_TFHE, euint128.unwrap(value), Common.EADDRESS_TFHE));
    }
    
    /// @notice Converts a euint256 to an ebool
    function asEbool(euint256 value) internal pure returns (ebool) {
        return ne(value, asEuint256(0));
    }
    /// @notice Converts a euint256 to an euint8
    function asEuint8(euint256 value) internal pure returns (euint8) {
        return euint8.wrap(Impl.cast(Common.EUINT256_TFHE, euint256.unwrap(value), Common.EUINT8_TFHE));
    }
    /// @notice Converts a euint256 to an euint16
    function asEuint16(euint256 value) internal pure returns (euint16) {
        return euint16.wrap(Impl.cast(Common.EUINT256_TFHE, euint256.unwrap(value), Common.EUINT16_TFHE));
    }
    /// @notice Converts a euint256 to an euint32
    function asEuint32(euint256 value) internal pure returns (euint32) {
        return euint32.wrap(Impl.cast(Common.EUINT256_TFHE, euint256.unwrap(value), Common.EUINT32_TFHE));
    }
    /// @notice Converts a euint256 to an euint64
    function asEuint64(euint256 value) internal pure returns (euint64) {
        return euint64.wrap(Impl.cast(Common.EUINT256_TFHE, euint256.unwrap(value), Common.EUINT64_TFHE));
    }
    /// @notice Converts a euint256 to an euint128
    function asEuint128(euint256 value) internal pure returns (euint128) {
        return euint128.wrap(Impl.cast(Common.EUINT256_TFHE, euint256.unwrap(value), Common.EUINT128_TFHE));
    }
    /// @notice Parses input ciphertexts from the user. Converts from encrypted raw bytes to an euint256
    /// @dev Also performs validation that the ciphertext is valid and has been encrypted using the network encryption key
    /// @return a ciphertext representation of the input
    function asEuint256(inEuint256 memory value) internal pure returns (euint256) {
        return FHE.asEuint256(value.data);
    }
    /// @notice Converts a euint256 to an eaddress
    function asEaddress(euint256 value) internal pure returns (eaddress) {
        return eaddress.wrap(Impl.cast(Common.EUINT256_TFHE, euint256.unwrap(value), Common.EADDRESS_TFHE));
    }
    
    /// @notice Converts a eaddress to an ebool
    function asEbool(eaddress value) internal pure returns (ebool) {
        return ne(value, asEaddress(0));
    }
    /// @notice Converts a eaddress to an euint8
    function asEuint8(eaddress value) internal pure returns (euint8) {
        return euint8.wrap(Impl.cast(Common.EADDRESS_TFHE, eaddress.unwrap(value), Common.EUINT8_TFHE));
    }
    /// @notice Converts a eaddress to an euint16
    function asEuint16(eaddress value) internal pure returns (euint16) {
        return euint16.wrap(Impl.cast(Common.EADDRESS_TFHE, eaddress.unwrap(value), Common.EUINT16_TFHE));
    }
    /// @notice Converts a eaddress to an euint32
    function asEuint32(eaddress value) internal pure returns (euint32) {
        return euint32.wrap(Impl.cast(Common.EADDRESS_TFHE, eaddress.unwrap(value), Common.EUINT32_TFHE));
    }
    /// @notice Converts a eaddress to an euint64
    function asEuint64(eaddress value) internal pure returns (euint64) {
        return euint64.wrap(Impl.cast(Common.EADDRESS_TFHE, eaddress.unwrap(value), Common.EUINT64_TFHE));
    }
    /// @notice Converts a eaddress to an euint128
    function asEuint128(eaddress value) internal pure returns (euint128) {
        return euint128.wrap(Impl.cast(Common.EADDRESS_TFHE, eaddress.unwrap(value), Common.EUINT128_TFHE));
    }
    /// @notice Converts a eaddress to an euint256
    function asEuint256(eaddress value) internal pure returns (euint256) {
        return euint256.wrap(Impl.cast(Common.EADDRESS_TFHE, eaddress.unwrap(value), Common.EUINT256_TFHE));
    }
    /// @notice Parses input ciphertexts from the user. Converts from encrypted raw bytes to an eaddress
    /// @dev Also performs validation that the ciphertext is valid and has been encrypted using the network encryption key
    /// @return a ciphertext representation of the input
    function asEaddress(inEaddress memory value) internal pure returns (eaddress) {
        return FHE.asEaddress(value.data);
    }
    /// @notice Converts a uint256 to an ebool
    function asEbool(uint256 value) internal pure returns (ebool) {
        return ebool.wrap(Impl.trivialEncrypt(value, Common.EBOOL_TFHE));
    }
    /// @notice Converts a uint256 to an euint8
    function asEuint8(uint256 value) internal pure returns (euint8) {
        return euint8.wrap(Impl.trivialEncrypt(value, Common.EUINT8_TFHE));
    }
    /// @notice Converts a uint256 to an euint16
    function asEuint16(uint256 value) internal pure returns (euint16) {
        return euint16.wrap(Impl.trivialEncrypt(value, Common.EUINT16_TFHE));
    }
    /// @notice Converts a uint256 to an euint32
    function asEuint32(uint256 value) internal pure returns (euint32) {
        return euint32.wrap(Impl.trivialEncrypt(value, Common.EUINT32_TFHE));
    }
    /// @notice Converts a uint256 to an euint64
    function asEuint64(uint256 value) internal pure returns (euint64) {
        return euint64.wrap(Impl.trivialEncrypt(value, Common.EUINT64_TFHE));
    }
    /// @notice Converts a uint256 to an euint128
    function asEuint128(uint256 value) internal pure returns (euint128) {
        return euint128.wrap(Impl.trivialEncrypt(value, Common.EUINT128_TFHE));
    }
    /// @notice Converts a uint256 to an euint256
    function asEuint256(uint256 value) internal pure returns (euint256) {
        return euint256.wrap(Impl.trivialEncrypt(value, Common.EUINT256_TFHE));
    }
    /// @notice Converts a uint256 to an eaddress
    function asEaddress(uint256 value) internal pure returns (eaddress) {
        return eaddress.wrap(Impl.trivialEncrypt(value, Common.EADDRESS_TFHE));
    }
    /// @notice Parses input ciphertexts from the user. Converts from encrypted raw bytes to an ebool
    /// @dev Also performs validation that the ciphertext is valid and has been encrypted using the network encryption key
    /// @return a ciphertext representation of the input
    function asEbool(bytes memory value) internal pure returns (ebool) {
        return ebool.wrap(Impl.verify(value, Common.EBOOL_TFHE));
    }
    /// @notice Parses input ciphertexts from the user. Converts from encrypted raw bytes to an euint8
    /// @dev Also performs validation that the ciphertext is valid and has been encrypted using the network encryption key
    /// @return a ciphertext representation of the input
    function asEuint8(bytes memory value) internal pure returns (euint8) {
        return euint8.wrap(Impl.verify(value, Common.EUINT8_TFHE));
    }
    /// @notice Parses input ciphertexts from the user. Converts from encrypted raw bytes to an euint16
    /// @dev Also performs validation that the ciphertext is valid and has been encrypted using the network encryption key
    /// @return a ciphertext representation of the input
    function asEuint16(bytes memory value) internal pure returns (euint16) {
        return euint16.wrap(Impl.verify(value, Common.EUINT16_TFHE));
    }
    /// @notice Parses input ciphertexts from the user. Converts from encrypted raw bytes to an euint32
    /// @dev Also performs validation that the ciphertext is valid and has been encrypted using the network encryption key
    /// @return a ciphertext representation of the input
    function asEuint32(bytes memory value) internal pure returns (euint32) {
        return euint32.wrap(Impl.verify(value, Common.EUINT32_TFHE));
    }
    /// @notice Parses input ciphertexts from the user. Converts from encrypted raw bytes to an euint64
    /// @dev Also performs validation that the ciphertext is valid and has been encrypted using the network encryption key
    /// @return a ciphertext representation of the input
    function asEuint64(bytes memory value) internal pure returns (euint64) {
        return euint64.wrap(Impl.verify(value, Common.EUINT64_TFHE));
    }
    /// @notice Parses input ciphertexts from the user. Converts from encrypted raw bytes to an euint128
    /// @dev Also performs validation that the ciphertext is valid and has been encrypted using the network encryption key
    /// @return a ciphertext representation of the input
    function asEuint128(bytes memory value) internal pure returns (euint128) {
        return euint128.wrap(Impl.verify(value, Common.EUINT128_TFHE));
    }
    /// @notice Parses input ciphertexts from the user. Converts from encrypted raw bytes to an euint256
    /// @dev Also performs validation that the ciphertext is valid and has been encrypted using the network encryption key
    /// @return a ciphertext representation of the input
    function asEuint256(bytes memory value) internal pure returns (euint256) {
        return euint256.wrap(Impl.verify(value, Common.EUINT256_TFHE));
    }
    /// @notice Parses input ciphertexts from the user. Converts from encrypted raw bytes to an eaddress
    /// @dev Also performs validation that the ciphertext is valid and has been encrypted using the network encryption key
    /// @return a ciphertext representation of the input
    function asEaddress(bytes memory value) internal pure returns (eaddress) {
        return eaddress.wrap(Impl.verify(value, Common.EADDRESS_TFHE));
    }
    /// @notice Converts a address to an eaddress
    /// Allows for a better user experience when working with eaddresses
    function asEaddress(address value) internal pure returns (eaddress) {
        return eaddress.wrap(Impl.trivialEncrypt(uint256(uint160(value)), Common.EADDRESS_TFHE));
    }
    /// @notice Converts a plaintext boolean value to a ciphertext ebool
    /// @dev Privacy: The input value is public, therefore the ciphertext should be considered public and should be used
    ///only for mathematical operations, not to represent data that should be private
    /// @return A ciphertext representation of the input 
    function asEbool(bool value) internal pure returns (ebool) {
        uint256 sVal = 0;
        if (value) {
            sVal = 1;
        }

        return asEbool(sVal);
    }
}

// ********** OPERATOR OVERLOADING ************* //

using {operatorAddEuint8 as +} for euint8 global;
/// @notice Performs the add operation
function operatorAddEuint8(euint8 lhs, euint8 rhs) pure returns (euint8) {
    return FHE.add(lhs, rhs);
}

using {operatorAddEuint16 as +} for euint16 global;
/// @notice Performs the add operation
function operatorAddEuint16(euint16 lhs, euint16 rhs) pure returns (euint16) {
    return FHE.add(lhs, rhs);
}

using {operatorAddEuint32 as +} for euint32 global;
/// @notice Performs the add operation
function operatorAddEuint32(euint32 lhs, euint32 rhs) pure returns (euint32) {
    return FHE.add(lhs, rhs);
}

using {operatorAddEuint64 as +} for euint64 global;
/// @notice Performs the add operation
function operatorAddEuint64(euint64 lhs, euint64 rhs) pure returns (euint64) {
    return FHE.add(lhs, rhs);
}

using {operatorAddEuint128 as +} for euint128 global;
/// @notice Performs the add operation
function operatorAddEuint128(euint128 lhs, euint128 rhs) pure returns (euint128) {
    return FHE.add(lhs, rhs);
}

using {operatorSubEuint8 as -} for euint8 global;
/// @notice Performs the sub operation
function operatorSubEuint8(euint8 lhs, euint8 rhs) pure returns (euint8) {
    return FHE.sub(lhs, rhs);
}

using {operatorSubEuint16 as -} for euint16 global;
/// @notice Performs the sub operation
function operatorSubEuint16(euint16 lhs, euint16 rhs) pure returns (euint16) {
    return FHE.sub(lhs, rhs);
}

using {operatorSubEuint32 as -} for euint32 global;
/// @notice Performs the sub operation
function operatorSubEuint32(euint32 lhs, euint32 rhs) pure returns (euint32) {
    return FHE.sub(lhs, rhs);
}

using {operatorSubEuint64 as -} for euint64 global;
/// @notice Performs the sub operation
function operatorSubEuint64(euint64 lhs, euint64 rhs) pure returns (euint64) {
    return FHE.sub(lhs, rhs);
}

using {operatorSubEuint128 as -} for euint128 global;
/// @notice Performs the sub operation
function operatorSubEuint128(euint128 lhs, euint128 rhs) pure returns (euint128) {
    return FHE.sub(lhs, rhs);
}

using {operatorMulEuint8 as *} for euint8 global;
/// @notice Performs the mul operation
function operatorMulEuint8(euint8 lhs, euint8 rhs) pure returns (euint8) {
    return FHE.mul(lhs, rhs);
}

using {operatorMulEuint16 as *} for euint16 global;
/// @notice Performs the mul operation
function operatorMulEuint16(euint16 lhs, euint16 rhs) pure returns (euint16) {
    return FHE.mul(lhs, rhs);
}

using {operatorMulEuint32 as *} for euint32 global;
/// @notice Performs the mul operation
function operatorMulEuint32(euint32 lhs, euint32 rhs) pure returns (euint32) {
    return FHE.mul(lhs, rhs);
}

using {operatorMulEuint64 as *} for euint64 global;
/// @notice Performs the mul operation
function operatorMulEuint64(euint64 lhs, euint64 rhs) pure returns (euint64) {
    return FHE.mul(lhs, rhs);
}

using {operatorDivEuint8 as /} for euint8 global;
/// @notice Performs the div operation
function operatorDivEuint8(euint8 lhs, euint8 rhs) pure returns (euint8) {
    return FHE.div(lhs, rhs);
}

using {operatorDivEuint16 as /} for euint16 global;
/// @notice Performs the div operation
function operatorDivEuint16(euint16 lhs, euint16 rhs) pure returns (euint16) {
    return FHE.div(lhs, rhs);
}

using {operatorDivEuint32 as /} for euint32 global;
/// @notice Performs the div operation
function operatorDivEuint32(euint32 lhs, euint32 rhs) pure returns (euint32) {
    return FHE.div(lhs, rhs);
}

using {operatorOrEbool as |} for ebool global;
/// @notice Performs the or operation
function operatorOrEbool(ebool lhs, ebool rhs) pure returns (ebool) {
    return FHE.or(lhs, rhs);
}

using {operatorOrEuint8 as |} for euint8 global;
/// @notice Performs the or operation
function operatorOrEuint8(euint8 lhs, euint8 rhs) pure returns (euint8) {
    return FHE.or(lhs, rhs);
}

using {operatorOrEuint16 as |} for euint16 global;
/// @notice Performs the or operation
function operatorOrEuint16(euint16 lhs, euint16 rhs) pure returns (euint16) {
    return FHE.or(lhs, rhs);
}

using {operatorOrEuint32 as |} for euint32 global;
/// @notice Performs the or operation
function operatorOrEuint32(euint32 lhs, euint32 rhs) pure returns (euint32) {
    return FHE.or(lhs, rhs);
}

using {operatorOrEuint64 as |} for euint64 global;
/// @notice Performs the or operation
function operatorOrEuint64(euint64 lhs, euint64 rhs) pure returns (euint64) {
    return FHE.or(lhs, rhs);
}

using {operatorOrEuint128 as |} for euint128 global;
/// @notice Performs the or operation
function operatorOrEuint128(euint128 lhs, euint128 rhs) pure returns (euint128) {
    return FHE.or(lhs, rhs);
}

using {operatorAndEbool as &} for ebool global;
/// @notice Performs the and operation
function operatorAndEbool(ebool lhs, ebool rhs) pure returns (ebool) {
    return FHE.and(lhs, rhs);
}

using {operatorAndEuint8 as &} for euint8 global;
/// @notice Performs the and operation
function operatorAndEuint8(euint8 lhs, euint8 rhs) pure returns (euint8) {
    return FHE.and(lhs, rhs);
}

using {operatorAndEuint16 as &} for euint16 global;
/// @notice Performs the and operation
function operatorAndEuint16(euint16 lhs, euint16 rhs) pure returns (euint16) {
    return FHE.and(lhs, rhs);
}

using {operatorAndEuint32 as &} for euint32 global;
/// @notice Performs the and operation
function operatorAndEuint32(euint32 lhs, euint32 rhs) pure returns (euint32) {
    return FHE.and(lhs, rhs);
}

using {operatorAndEuint64 as &} for euint64 global;
/// @notice Performs the and operation
function operatorAndEuint64(euint64 lhs, euint64 rhs) pure returns (euint64) {
    return FHE.and(lhs, rhs);
}

using {operatorAndEuint128 as &} for euint128 global;
/// @notice Performs the and operation
function operatorAndEuint128(euint128 lhs, euint128 rhs) pure returns (euint128) {
    return FHE.and(lhs, rhs);
}

using {operatorXorEbool as ^} for ebool global;
/// @notice Performs the xor operation
function operatorXorEbool(ebool lhs, ebool rhs) pure returns (ebool) {
    return FHE.xor(lhs, rhs);
}

using {operatorXorEuint8 as ^} for euint8 global;
/// @notice Performs the xor operation
function operatorXorEuint8(euint8 lhs, euint8 rhs) pure returns (euint8) {
    return FHE.xor(lhs, rhs);
}

using {operatorXorEuint16 as ^} for euint16 global;
/// @notice Performs the xor operation
function operatorXorEuint16(euint16 lhs, euint16 rhs) pure returns (euint16) {
    return FHE.xor(lhs, rhs);
}

using {operatorXorEuint32 as ^} for euint32 global;
/// @notice Performs the xor operation
function operatorXorEuint32(euint32 lhs, euint32 rhs) pure returns (euint32) {
    return FHE.xor(lhs, rhs);
}

using {operatorXorEuint64 as ^} for euint64 global;
/// @notice Performs the xor operation
function operatorXorEuint64(euint64 lhs, euint64 rhs) pure returns (euint64) {
    return FHE.xor(lhs, rhs);
}

using {operatorXorEuint128 as ^} for euint128 global;
/// @notice Performs the xor operation
function operatorXorEuint128(euint128 lhs, euint128 rhs) pure returns (euint128) {
    return FHE.xor(lhs, rhs);
}

using {operatorRemEuint8 as %} for euint8 global;
/// @notice Performs the rem operation
function operatorRemEuint8(euint8 lhs, euint8 rhs) pure returns (euint8) {
    return FHE.rem(lhs, rhs);
}

using {operatorRemEuint16 as %} for euint16 global;
/// @notice Performs the rem operation
function operatorRemEuint16(euint16 lhs, euint16 rhs) pure returns (euint16) {
    return FHE.rem(lhs, rhs);
}

using {operatorRemEuint32 as %} for euint32 global;
/// @notice Performs the rem operation
function operatorRemEuint32(euint32 lhs, euint32 rhs) pure returns (euint32) {
    return FHE.rem(lhs, rhs);
}

// ********** BINDING DEFS ************* //

using BindingsEbool for ebool global;
library BindingsEbool {
    
    /// @notice Performs the eq operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type ebool
    /// @return the result of the eq
    function eq(ebool lhs, ebool rhs) internal pure returns (ebool) {
        return FHE.eq(lhs, rhs);
    }
    
    /// @notice Performs the ne operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type ebool
    /// @return the result of the ne
    function ne(ebool lhs, ebool rhs) internal pure returns (ebool) {
        return FHE.ne(lhs, rhs);
    }
    
    /// @notice Performs the and operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type ebool
    /// @return the result of the and
    function and(ebool lhs, ebool rhs) internal pure returns (ebool) {
        return FHE.and(lhs, rhs);
    }
    
    /// @notice Performs the or operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type ebool
    /// @return the result of the or
    function or(ebool lhs, ebool rhs) internal pure returns (ebool) {
        return FHE.or(lhs, rhs);
    }
    
    /// @notice Performs the xor operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type ebool
    /// @return the result of the xor
    function xor(ebool lhs, ebool rhs) internal pure returns (ebool) {
        return FHE.xor(lhs, rhs);
    }
    function toU8(ebool value) internal pure returns (euint8) {
        return FHE.asEuint8(value);
    }
    function toU16(ebool value) internal pure returns (euint16) {
        return FHE.asEuint16(value);
    }
    function toU32(ebool value) internal pure returns (euint32) {
        return FHE.asEuint32(value);
    }
    function toU64(ebool value) internal pure returns (euint64) {
        return FHE.asEuint64(value);
    }
    function toU128(ebool value) internal pure returns (euint128) {
        return FHE.asEuint128(value);
    }
    function toU256(ebool value) internal pure returns (euint256) {
        return FHE.asEuint256(value);
    }
    function toEaddress(ebool value) internal pure returns (eaddress) {
        return FHE.asEaddress(value);
    }
    function seal(ebool value, bytes32 publicKey) internal pure returns (string memory) {
        return FHE.sealoutput(value, publicKey);
    }
    function decrypt(ebool value) internal pure returns (bool) {
        return FHE.decrypt(value);
    }
}

using BindingsEuint8 for euint8 global;
library BindingsEuint8 {
    
    /// @notice Performs the add operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint8
    /// @return the result of the add
    function add(euint8 lhs, euint8 rhs) internal pure returns (euint8) {
        return FHE.add(lhs, rhs);
    }
    
    /// @notice Performs the mul operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint8
    /// @return the result of the mul
    function mul(euint8 lhs, euint8 rhs) internal pure returns (euint8) {
        return FHE.mul(lhs, rhs);
    }
    
    /// @notice Performs the div operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint8
    /// @return the result of the div
    function div(euint8 lhs, euint8 rhs) internal pure returns (euint8) {
        return FHE.div(lhs, rhs);
    }
    
    /// @notice Performs the sub operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint8
    /// @return the result of the sub
    function sub(euint8 lhs, euint8 rhs) internal pure returns (euint8) {
        return FHE.sub(lhs, rhs);
    }
    
    /// @notice Performs the eq operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint8
    /// @return the result of the eq
    function eq(euint8 lhs, euint8 rhs) internal pure returns (ebool) {
        return FHE.eq(lhs, rhs);
    }
    
    /// @notice Performs the ne operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint8
    /// @return the result of the ne
    function ne(euint8 lhs, euint8 rhs) internal pure returns (ebool) {
        return FHE.ne(lhs, rhs);
    }
    
    /// @notice Performs the and operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint8
    /// @return the result of the and
    function and(euint8 lhs, euint8 rhs) internal pure returns (euint8) {
        return FHE.and(lhs, rhs);
    }
    
    /// @notice Performs the or operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint8
    /// @return the result of the or
    function or(euint8 lhs, euint8 rhs) internal pure returns (euint8) {
        return FHE.or(lhs, rhs);
    }
    
    /// @notice Performs the xor operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint8
    /// @return the result of the xor
    function xor(euint8 lhs, euint8 rhs) internal pure returns (euint8) {
        return FHE.xor(lhs, rhs);
    }
    
    /// @notice Performs the gt operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint8
    /// @return the result of the gt
    function gt(euint8 lhs, euint8 rhs) internal pure returns (ebool) {
        return FHE.gt(lhs, rhs);
    }
    
    /// @notice Performs the gte operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint8
    /// @return the result of the gte
    function gte(euint8 lhs, euint8 rhs) internal pure returns (ebool) {
        return FHE.gte(lhs, rhs);
    }
    
    /// @notice Performs the lt operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint8
    /// @return the result of the lt
    function lt(euint8 lhs, euint8 rhs) internal pure returns (ebool) {
        return FHE.lt(lhs, rhs);
    }
    
    /// @notice Performs the lte operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint8
    /// @return the result of the lte
    function lte(euint8 lhs, euint8 rhs) internal pure returns (ebool) {
        return FHE.lte(lhs, rhs);
    }
    
    /// @notice Performs the rem operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint8
    /// @return the result of the rem
    function rem(euint8 lhs, euint8 rhs) internal pure returns (euint8) {
        return FHE.rem(lhs, rhs);
    }
    
    /// @notice Performs the max operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint8
    /// @return the result of the max
    function max(euint8 lhs, euint8 rhs) internal pure returns (euint8) {
        return FHE.max(lhs, rhs);
    }
    
    /// @notice Performs the min operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint8
    /// @return the result of the min
    function min(euint8 lhs, euint8 rhs) internal pure returns (euint8) {
        return FHE.min(lhs, rhs);
    }
    
    /// @notice Performs the shl operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint8
    /// @return the result of the shl
    function shl(euint8 lhs, euint8 rhs) internal pure returns (euint8) {
        return FHE.shl(lhs, rhs);
    }
    
    /// @notice Performs the shr operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint8
    /// @return the result of the shr
    function shr(euint8 lhs, euint8 rhs) internal pure returns (euint8) {
        return FHE.shr(lhs, rhs);
    }
    function toBool(euint8 value) internal pure returns (ebool) {
        return FHE.asEbool(value);
    }
    function toU16(euint8 value) internal pure returns (euint16) {
        return FHE.asEuint16(value);
    }
    function toU32(euint8 value) internal pure returns (euint32) {
        return FHE.asEuint32(value);
    }
    function toU64(euint8 value) internal pure returns (euint64) {
        return FHE.asEuint64(value);
    }
    function toU128(euint8 value) internal pure returns (euint128) {
        return FHE.asEuint128(value);
    }
    function toU256(euint8 value) internal pure returns (euint256) {
        return FHE.asEuint256(value);
    }
    function toEaddress(euint8 value) internal pure returns (eaddress) {
        return FHE.asEaddress(value);
    }
    function seal(euint8 value, bytes32 publicKey) internal pure returns (string memory) {
        return FHE.sealoutput(value, publicKey);
    }
    function decrypt(euint8 value) internal pure returns (uint8) {
        return FHE.decrypt(value);
    }
}

using BindingsEuint16 for euint16 global;
library BindingsEuint16 {
    
    /// @notice Performs the add operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint16
    /// @return the result of the add
    function add(euint16 lhs, euint16 rhs) internal pure returns (euint16) {
        return FHE.add(lhs, rhs);
    }
    
    /// @notice Performs the mul operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint16
    /// @return the result of the mul
    function mul(euint16 lhs, euint16 rhs) internal pure returns (euint16) {
        return FHE.mul(lhs, rhs);
    }
    
    /// @notice Performs the div operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint16
    /// @return the result of the div
    function div(euint16 lhs, euint16 rhs) internal pure returns (euint16) {
        return FHE.div(lhs, rhs);
    }
    
    /// @notice Performs the sub operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint16
    /// @return the result of the sub
    function sub(euint16 lhs, euint16 rhs) internal pure returns (euint16) {
        return FHE.sub(lhs, rhs);
    }
    
    /// @notice Performs the eq operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint16
    /// @return the result of the eq
    function eq(euint16 lhs, euint16 rhs) internal pure returns (ebool) {
        return FHE.eq(lhs, rhs);
    }
    
    /// @notice Performs the ne operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint16
    /// @return the result of the ne
    function ne(euint16 lhs, euint16 rhs) internal pure returns (ebool) {
        return FHE.ne(lhs, rhs);
    }
    
    /// @notice Performs the and operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint16
    /// @return the result of the and
    function and(euint16 lhs, euint16 rhs) internal pure returns (euint16) {
        return FHE.and(lhs, rhs);
    }
    
    /// @notice Performs the or operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint16
    /// @return the result of the or
    function or(euint16 lhs, euint16 rhs) internal pure returns (euint16) {
        return FHE.or(lhs, rhs);
    }
    
    /// @notice Performs the xor operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint16
    /// @return the result of the xor
    function xor(euint16 lhs, euint16 rhs) internal pure returns (euint16) {
        return FHE.xor(lhs, rhs);
    }
    
    /// @notice Performs the gt operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint16
    /// @return the result of the gt
    function gt(euint16 lhs, euint16 rhs) internal pure returns (ebool) {
        return FHE.gt(lhs, rhs);
    }
    
    /// @notice Performs the gte operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint16
    /// @return the result of the gte
    function gte(euint16 lhs, euint16 rhs) internal pure returns (ebool) {
        return FHE.gte(lhs, rhs);
    }
    
    /// @notice Performs the lt operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint16
    /// @return the result of the lt
    function lt(euint16 lhs, euint16 rhs) internal pure returns (ebool) {
        return FHE.lt(lhs, rhs);
    }
    
    /// @notice Performs the lte operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint16
    /// @return the result of the lte
    function lte(euint16 lhs, euint16 rhs) internal pure returns (ebool) {
        return FHE.lte(lhs, rhs);
    }
    
    /// @notice Performs the rem operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint16
    /// @return the result of the rem
    function rem(euint16 lhs, euint16 rhs) internal pure returns (euint16) {
        return FHE.rem(lhs, rhs);
    }
    
    /// @notice Performs the max operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint16
    /// @return the result of the max
    function max(euint16 lhs, euint16 rhs) internal pure returns (euint16) {
        return FHE.max(lhs, rhs);
    }
    
    /// @notice Performs the min operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint16
    /// @return the result of the min
    function min(euint16 lhs, euint16 rhs) internal pure returns (euint16) {
        return FHE.min(lhs, rhs);
    }
    
    /// @notice Performs the shl operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint16
    /// @return the result of the shl
    function shl(euint16 lhs, euint16 rhs) internal pure returns (euint16) {
        return FHE.shl(lhs, rhs);
    }
    
    /// @notice Performs the shr operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint16
    /// @return the result of the shr
    function shr(euint16 lhs, euint16 rhs) internal pure returns (euint16) {
        return FHE.shr(lhs, rhs);
    }
    function toBool(euint16 value) internal pure returns (ebool) {
        return FHE.asEbool(value);
    }
    function toU8(euint16 value) internal pure returns (euint8) {
        return FHE.asEuint8(value);
    }
    function toU32(euint16 value) internal pure returns (euint32) {
        return FHE.asEuint32(value);
    }
    function toU64(euint16 value) internal pure returns (euint64) {
        return FHE.asEuint64(value);
    }
    function toU128(euint16 value) internal pure returns (euint128) {
        return FHE.asEuint128(value);
    }
    function toU256(euint16 value) internal pure returns (euint256) {
        return FHE.asEuint256(value);
    }
    function toEaddress(euint16 value) internal pure returns (eaddress) {
        return FHE.asEaddress(value);
    }
    function seal(euint16 value, bytes32 publicKey) internal pure returns (string memory) {
        return FHE.sealoutput(value, publicKey);
    }
    function decrypt(euint16 value) internal pure returns (uint16) {
        return FHE.decrypt(value);
    }
}

using BindingsEuint32 for euint32 global;
library BindingsEuint32 {
    
    /// @notice Performs the add operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint32
    /// @return the result of the add
    function add(euint32 lhs, euint32 rhs) internal pure returns (euint32) {
        return FHE.add(lhs, rhs);
    }
    
    /// @notice Performs the mul operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint32
    /// @return the result of the mul
    function mul(euint32 lhs, euint32 rhs) internal pure returns (euint32) {
        return FHE.mul(lhs, rhs);
    }
    
    /// @notice Performs the div operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint32
    /// @return the result of the div
    function div(euint32 lhs, euint32 rhs) internal pure returns (euint32) {
        return FHE.div(lhs, rhs);
    }
    
    /// @notice Performs the sub operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint32
    /// @return the result of the sub
    function sub(euint32 lhs, euint32 rhs) internal pure returns (euint32) {
        return FHE.sub(lhs, rhs);
    }
    
    /// @notice Performs the eq operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint32
    /// @return the result of the eq
    function eq(euint32 lhs, euint32 rhs) internal pure returns (ebool) {
        return FHE.eq(lhs, rhs);
    }
    
    /// @notice Performs the ne operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint32
    /// @return the result of the ne
    function ne(euint32 lhs, euint32 rhs) internal pure returns (ebool) {
        return FHE.ne(lhs, rhs);
    }
    
    /// @notice Performs the and operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint32
    /// @return the result of the and
    function and(euint32 lhs, euint32 rhs) internal pure returns (euint32) {
        return FHE.and(lhs, rhs);
    }
    
    /// @notice Performs the or operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint32
    /// @return the result of the or
    function or(euint32 lhs, euint32 rhs) internal pure returns (euint32) {
        return FHE.or(lhs, rhs);
    }
    
    /// @notice Performs the xor operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint32
    /// @return the result of the xor
    function xor(euint32 lhs, euint32 rhs) internal pure returns (euint32) {
        return FHE.xor(lhs, rhs);
    }
    
    /// @notice Performs the gt operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint32
    /// @return the result of the gt
    function gt(euint32 lhs, euint32 rhs) internal pure returns (ebool) {
        return FHE.gt(lhs, rhs);
    }
    
    /// @notice Performs the gte operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint32
    /// @return the result of the gte
    function gte(euint32 lhs, euint32 rhs) internal pure returns (ebool) {
        return FHE.gte(lhs, rhs);
    }
    
    /// @notice Performs the lt operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint32
    /// @return the result of the lt
    function lt(euint32 lhs, euint32 rhs) internal pure returns (ebool) {
        return FHE.lt(lhs, rhs);
    }
    
    /// @notice Performs the lte operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint32
    /// @return the result of the lte
    function lte(euint32 lhs, euint32 rhs) internal pure returns (ebool) {
        return FHE.lte(lhs, rhs);
    }
    
    /// @notice Performs the rem operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint32
    /// @return the result of the rem
    function rem(euint32 lhs, euint32 rhs) internal pure returns (euint32) {
        return FHE.rem(lhs, rhs);
    }
    
    /// @notice Performs the max operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint32
    /// @return the result of the max
    function max(euint32 lhs, euint32 rhs) internal pure returns (euint32) {
        return FHE.max(lhs, rhs);
    }
    
    /// @notice Performs the min operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint32
    /// @return the result of the min
    function min(euint32 lhs, euint32 rhs) internal pure returns (euint32) {
        return FHE.min(lhs, rhs);
    }
    
    /// @notice Performs the shl operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint32
    /// @return the result of the shl
    function shl(euint32 lhs, euint32 rhs) internal pure returns (euint32) {
        return FHE.shl(lhs, rhs);
    }
    
    /// @notice Performs the shr operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint32
    /// @return the result of the shr
    function shr(euint32 lhs, euint32 rhs) internal pure returns (euint32) {
        return FHE.shr(lhs, rhs);
    }
    function toBool(euint32 value) internal pure returns (ebool) {
        return FHE.asEbool(value);
    }
    function toU8(euint32 value) internal pure returns (euint8) {
        return FHE.asEuint8(value);
    }
    function toU16(euint32 value) internal pure returns (euint16) {
        return FHE.asEuint16(value);
    }
    function toU64(euint32 value) internal pure returns (euint64) {
        return FHE.asEuint64(value);
    }
    function toU128(euint32 value) internal pure returns (euint128) {
        return FHE.asEuint128(value);
    }
    function toU256(euint32 value) internal pure returns (euint256) {
        return FHE.asEuint256(value);
    }
    function toEaddress(euint32 value) internal pure returns (eaddress) {
        return FHE.asEaddress(value);
    }
    function seal(euint32 value, bytes32 publicKey) internal pure returns (string memory) {
        return FHE.sealoutput(value, publicKey);
    }
    function decrypt(euint32 value) internal pure returns (uint32) {
        return FHE.decrypt(value);
    }
}

using BindingsEuint64 for euint64 global;
library BindingsEuint64 {
    
    /// @notice Performs the add operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint64
    /// @return the result of the add
    function add(euint64 lhs, euint64 rhs) internal pure returns (euint64) {
        return FHE.add(lhs, rhs);
    }
    
    /// @notice Performs the mul operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint64
    /// @return the result of the mul
    function mul(euint64 lhs, euint64 rhs) internal pure returns (euint64) {
        return FHE.mul(lhs, rhs);
    }
    
    /// @notice Performs the sub operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint64
    /// @return the result of the sub
    function sub(euint64 lhs, euint64 rhs) internal pure returns (euint64) {
        return FHE.sub(lhs, rhs);
    }
    
    /// @notice Performs the eq operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint64
    /// @return the result of the eq
    function eq(euint64 lhs, euint64 rhs) internal pure returns (ebool) {
        return FHE.eq(lhs, rhs);
    }
    
    /// @notice Performs the ne operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint64
    /// @return the result of the ne
    function ne(euint64 lhs, euint64 rhs) internal pure returns (ebool) {
        return FHE.ne(lhs, rhs);
    }
    
    /// @notice Performs the and operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint64
    /// @return the result of the and
    function and(euint64 lhs, euint64 rhs) internal pure returns (euint64) {
        return FHE.and(lhs, rhs);
    }
    
    /// @notice Performs the or operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint64
    /// @return the result of the or
    function or(euint64 lhs, euint64 rhs) internal pure returns (euint64) {
        return FHE.or(lhs, rhs);
    }
    
    /// @notice Performs the xor operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint64
    /// @return the result of the xor
    function xor(euint64 lhs, euint64 rhs) internal pure returns (euint64) {
        return FHE.xor(lhs, rhs);
    }
    
    /// @notice Performs the gt operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint64
    /// @return the result of the gt
    function gt(euint64 lhs, euint64 rhs) internal pure returns (ebool) {
        return FHE.gt(lhs, rhs);
    }
    
    /// @notice Performs the gte operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint64
    /// @return the result of the gte
    function gte(euint64 lhs, euint64 rhs) internal pure returns (ebool) {
        return FHE.gte(lhs, rhs);
    }
    
    /// @notice Performs the lt operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint64
    /// @return the result of the lt
    function lt(euint64 lhs, euint64 rhs) internal pure returns (ebool) {
        return FHE.lt(lhs, rhs);
    }
    
    /// @notice Performs the lte operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint64
    /// @return the result of the lte
    function lte(euint64 lhs, euint64 rhs) internal pure returns (ebool) {
        return FHE.lte(lhs, rhs);
    }
    
    /// @notice Performs the max operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint64
    /// @return the result of the max
    function max(euint64 lhs, euint64 rhs) internal pure returns (euint64) {
        return FHE.max(lhs, rhs);
    }
    
    /// @notice Performs the min operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint64
    /// @return the result of the min
    function min(euint64 lhs, euint64 rhs) internal pure returns (euint64) {
        return FHE.min(lhs, rhs);
    }
    
    /// @notice Performs the shl operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint64
    /// @return the result of the shl
    function shl(euint64 lhs, euint64 rhs) internal pure returns (euint64) {
        return FHE.shl(lhs, rhs);
    }
    
    /// @notice Performs the shr operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint64
    /// @return the result of the shr
    function shr(euint64 lhs, euint64 rhs) internal pure returns (euint64) {
        return FHE.shr(lhs, rhs);
    }
    function toBool(euint64 value) internal pure returns (ebool) {
        return FHE.asEbool(value);
    }
    function toU8(euint64 value) internal pure returns (euint8) {
        return FHE.asEuint8(value);
    }
    function toU16(euint64 value) internal pure returns (euint16) {
        return FHE.asEuint16(value);
    }
    function toU32(euint64 value) internal pure returns (euint32) {
        return FHE.asEuint32(value);
    }
    function toU128(euint64 value) internal pure returns (euint128) {
        return FHE.asEuint128(value);
    }
    function toU256(euint64 value) internal pure returns (euint256) {
        return FHE.asEuint256(value);
    }
    function toEaddress(euint64 value) internal pure returns (eaddress) {
        return FHE.asEaddress(value);
    }
    function seal(euint64 value, bytes32 publicKey) internal pure returns (string memory) {
        return FHE.sealoutput(value, publicKey);
    }
    function decrypt(euint64 value) internal pure returns (uint64) {
        return FHE.decrypt(value);
    }
}

using BindingsEuint128 for euint128 global;
library BindingsEuint128 {
    
    /// @notice Performs the add operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint128
    /// @return the result of the add
    function add(euint128 lhs, euint128 rhs) internal pure returns (euint128) {
        return FHE.add(lhs, rhs);
    }
    
    /// @notice Performs the sub operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint128
    /// @return the result of the sub
    function sub(euint128 lhs, euint128 rhs) internal pure returns (euint128) {
        return FHE.sub(lhs, rhs);
    }
    
    /// @notice Performs the eq operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint128
    /// @return the result of the eq
    function eq(euint128 lhs, euint128 rhs) internal pure returns (ebool) {
        return FHE.eq(lhs, rhs);
    }
    
    /// @notice Performs the ne operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint128
    /// @return the result of the ne
    function ne(euint128 lhs, euint128 rhs) internal pure returns (ebool) {
        return FHE.ne(lhs, rhs);
    }
    
    /// @notice Performs the and operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint128
    /// @return the result of the and
    function and(euint128 lhs, euint128 rhs) internal pure returns (euint128) {
        return FHE.and(lhs, rhs);
    }
    
    /// @notice Performs the or operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint128
    /// @return the result of the or
    function or(euint128 lhs, euint128 rhs) internal pure returns (euint128) {
        return FHE.or(lhs, rhs);
    }
    
    /// @notice Performs the xor operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint128
    /// @return the result of the xor
    function xor(euint128 lhs, euint128 rhs) internal pure returns (euint128) {
        return FHE.xor(lhs, rhs);
    }
    
    /// @notice Performs the gt operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint128
    /// @return the result of the gt
    function gt(euint128 lhs, euint128 rhs) internal pure returns (ebool) {
        return FHE.gt(lhs, rhs);
    }
    
    /// @notice Performs the gte operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint128
    /// @return the result of the gte
    function gte(euint128 lhs, euint128 rhs) internal pure returns (ebool) {
        return FHE.gte(lhs, rhs);
    }
    
    /// @notice Performs the lt operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint128
    /// @return the result of the lt
    function lt(euint128 lhs, euint128 rhs) internal pure returns (ebool) {
        return FHE.lt(lhs, rhs);
    }
    
    /// @notice Performs the lte operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint128
    /// @return the result of the lte
    function lte(euint128 lhs, euint128 rhs) internal pure returns (ebool) {
        return FHE.lte(lhs, rhs);
    }
    
    /// @notice Performs the max operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint128
    /// @return the result of the max
    function max(euint128 lhs, euint128 rhs) internal pure returns (euint128) {
        return FHE.max(lhs, rhs);
    }
    
    /// @notice Performs the min operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint128
    /// @return the result of the min
    function min(euint128 lhs, euint128 rhs) internal pure returns (euint128) {
        return FHE.min(lhs, rhs);
    }
    
    /// @notice Performs the shl operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint128
    /// @return the result of the shl
    function shl(euint128 lhs, euint128 rhs) internal pure returns (euint128) {
        return FHE.shl(lhs, rhs);
    }
    
    /// @notice Performs the shr operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint128
    /// @return the result of the shr
    function shr(euint128 lhs, euint128 rhs) internal pure returns (euint128) {
        return FHE.shr(lhs, rhs);
    }
    function toBool(euint128 value) internal pure returns (ebool) {
        return FHE.asEbool(value);
    }
    function toU8(euint128 value) internal pure returns (euint8) {
        return FHE.asEuint8(value);
    }
    function toU16(euint128 value) internal pure returns (euint16) {
        return FHE.asEuint16(value);
    }
    function toU32(euint128 value) internal pure returns (euint32) {
        return FHE.asEuint32(value);
    }
    function toU64(euint128 value) internal pure returns (euint64) {
        return FHE.asEuint64(value);
    }
    function toU256(euint128 value) internal pure returns (euint256) {
        return FHE.asEuint256(value);
    }
    function toEaddress(euint128 value) internal pure returns (eaddress) {
        return FHE.asEaddress(value);
    }
    function seal(euint128 value, bytes32 publicKey) internal pure returns (string memory) {
        return FHE.sealoutput(value, publicKey);
    }
    function decrypt(euint128 value) internal pure returns (uint128) {
        return FHE.decrypt(value);
    }
}

using BindingsEuint256 for euint256 global;
library BindingsEuint256 {
    
    /// @notice Performs the eq operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint256
    /// @return the result of the eq
    function eq(euint256 lhs, euint256 rhs) internal pure returns (ebool) {
        return FHE.eq(lhs, rhs);
    }
    
    /// @notice Performs the ne operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type euint256
    /// @return the result of the ne
    function ne(euint256 lhs, euint256 rhs) internal pure returns (ebool) {
        return FHE.ne(lhs, rhs);
    }
    function toBool(euint256 value) internal pure returns (ebool) {
        return FHE.asEbool(value);
    }
    function toU8(euint256 value) internal pure returns (euint8) {
        return FHE.asEuint8(value);
    }
    function toU16(euint256 value) internal pure returns (euint16) {
        return FHE.asEuint16(value);
    }
    function toU32(euint256 value) internal pure returns (euint32) {
        return FHE.asEuint32(value);
    }
    function toU64(euint256 value) internal pure returns (euint64) {
        return FHE.asEuint64(value);
    }
    function toU128(euint256 value) internal pure returns (euint128) {
        return FHE.asEuint128(value);
    }
    function toEaddress(euint256 value) internal pure returns (eaddress) {
        return FHE.asEaddress(value);
    }
    function seal(euint256 value, bytes32 publicKey) internal pure returns (string memory) {
        return FHE.sealoutput(value, publicKey);
    }
    function decrypt(euint256 value) internal pure returns (uint256) {
        return FHE.decrypt(value);
    }
}

using BindingsEaddress for eaddress global;
library BindingsEaddress {
    
    /// @notice Performs the eq operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type eaddress
    /// @return the result of the eq
    function eq(eaddress lhs, eaddress rhs) internal pure returns (ebool) {
        return FHE.eq(lhs, rhs);
    }
    
    /// @notice Performs the ne operation
    /// @dev Pure in this function is marked as a hack/workaround - note that this function is NOT pure as fetches of ciphertexts require state access
    /// @param lhs input of type eaddress
    /// @return the result of the ne
    function ne(eaddress lhs, eaddress rhs) internal pure returns (ebool) {
        return FHE.ne(lhs, rhs);
    }
    function toBool(eaddress value) internal pure returns (ebool) {
        return FHE.asEbool(value);
    }
    function toU8(eaddress value) internal pure returns (euint8) {
        return FHE.asEuint8(value);
    }
    function toU16(eaddress value) internal pure returns (euint16) {
        return FHE.asEuint16(value);
    }
    function toU32(eaddress value) internal pure returns (euint32) {
        return FHE.asEuint32(value);
    }
    function toU64(eaddress value) internal pure returns (euint64) {
        return FHE.asEuint64(value);
    }
    function toU128(eaddress value) internal pure returns (euint128) {
        return FHE.asEuint128(value);
    }
    function toU256(eaddress value) internal pure returns (euint256) {
        return FHE.asEuint256(value);
    }
    function seal(eaddress value, bytes32 publicKey) internal pure returns (string memory) {
        return FHE.sealoutput(value, publicKey);
    }
    function decrypt(eaddress value) internal pure returns (address) {
        return FHE.decrypt(value);
    }
}

// lib/openzeppelin-contracts/contracts/utils/ShortStrings.sol

// OpenZeppelin Contracts (last updated v5.0.0) (utils/ShortStrings.sol)

// | string  | 0xAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA   |
// | length  | 0x                                                              BB |
type ShortString is bytes32;

/**
 * @dev This library provides functions to convert short memory strings
 * into a `ShortString` type that can be used as an immutable variable.
 *
 * Strings of arbitrary length can be optimized using this library if
 * they are short enough (up to 31 bytes) by packing them with their
 * length (1 byte) in a single EVM word (32 bytes). Additionally, a
 * fallback mechanism can be used for every other case.
 *
 * Usage example:
 *
 * ```solidity
 * contract Named {
 *     using ShortStrings for *;
 *
 *     ShortString private immutable _name;
 *     string private _nameFallback;
 *
 *     constructor(string memory contractName) {
 *         _name = contractName.toShortStringWithFallback(_nameFallback);
 *     }
 *
 *     function name() external view returns (string memory) {
 *         return _name.toStringWithFallback(_nameFallback);
 *     }
 * }
 * ```
 */
library ShortStrings {
    // Used as an identifier for strings longer than 31 bytes.
    bytes32 private constant FALLBACK_SENTINEL = 0x00000000000000000000000000000000000000000000000000000000000000FF;

    error StringTooLong(string str);
    error InvalidShortString();

    /**
     * @dev Encode a string of at most 31 chars into a `ShortString`.
     *
     * This will trigger a `StringTooLong` error is the input string is too long.
     */
    function toShortString(string memory str) internal pure returns (ShortString) {
        bytes memory bstr = bytes(str);
        if (bstr.length > 31) {
            revert StringTooLong(str);
        }
        return ShortString.wrap(bytes32(uint256(bytes32(bstr)) | bstr.length));
    }

    /**
     * @dev Decode a `ShortString` back to a "normal" string.
     */
    function toString(ShortString sstr) internal pure returns (string memory) {
        uint256 len = byteLength(sstr);
        // using `new string(len)` would work locally but is not memory safe.
        string memory str = new string(32);
        /// @solidity memory-safe-assembly
        assembly {
            mstore(str, len)
            mstore(add(str, 0x20), sstr)
        }
        return str;
    }

    /**
     * @dev Return the length of a `ShortString`.
     */
    function byteLength(ShortString sstr) internal pure returns (uint256) {
        uint256 result = uint256(ShortString.unwrap(sstr)) & 0xFF;
        if (result > 31) {
            revert InvalidShortString();
        }
        return result;
    }

    /**
     * @dev Encode a string into a `ShortString`, or write it to storage if it is too long.
     */
    function toShortStringWithFallback(string memory value, string storage store) internal returns (ShortString) {
        if (bytes(value).length < 32) {
            return toShortString(value);
        } else {
            StorageSlot.getStringSlot(store).value = value;
            return ShortString.wrap(FALLBACK_SENTINEL);
        }
    }

    /**
     * @dev Decode a string that was encoded to `ShortString` or written to storage using {setWithFallback}.
     */
    function toStringWithFallback(ShortString value, string storage store) internal pure returns (string memory) {
        if (ShortString.unwrap(value) != FALLBACK_SENTINEL) {
            return toString(value);
        } else {
            return store;
        }
    }

    /**
     * @dev Return the length of a string that was encoded to `ShortString` or written to storage using
     * {setWithFallback}.
     *
     * WARNING: This will return the "byte length" of the string. This may not reflect the actual length in terms of
     * actual characters as the UTF-8 encoding of a single character can span over multiple bytes.
     */
    function byteLengthWithFallback(ShortString value, string storage store) internal view returns (uint256) {
        if (ShortString.unwrap(value) != FALLBACK_SENTINEL) {
            return byteLength(value);
        } else {
            return bytes(store).length;
        }
    }
}

// lib/openzeppelin-contracts/contracts/utils/Strings.sol

// OpenZeppelin Contracts (last updated v5.0.0) (utils/Strings.sol)

/**
 * @dev String operations.
 */
library Strings {
    bytes16 private constant HEX_DIGITS = "0123456789abcdef";
    uint8 private constant ADDRESS_LENGTH = 20;

    /**
     * @dev The `value` string doesn't fit in the specified `length`.
     */
    error StringsInsufficientHexLength(uint256 value, uint256 length);

    /**
     * @dev Converts a `uint256` to its ASCII `string` decimal representation.
     */
    function toString(uint256 value) internal pure returns (string memory) {
        unchecked {
            uint256 length = Math.log10(value) + 1;
            string memory buffer = new string(length);
            uint256 ptr;
            /// @solidity memory-safe-assembly
            assembly {
                ptr := add(buffer, add(32, length))
            }
            while (true) {
                ptr--;
                /// @solidity memory-safe-assembly
                assembly {
                    mstore8(ptr, byte(mod(value, 10), HEX_DIGITS))
                }
                value /= 10;
                if (value == 0) break;
            }
            return buffer;
        }
    }

    /**
     * @dev Converts a `int256` to its ASCII `string` decimal representation.
     */
    function toStringSigned(int256 value) internal pure returns (string memory) {
        return string.concat(value < 0 ? "-" : "", toString(SignedMath.abs(value)));
    }

    /**
     * @dev Converts a `uint256` to its ASCII `string` hexadecimal representation.
     */
    function toHexString(uint256 value) internal pure returns (string memory) {
        unchecked {
            return toHexString(value, Math.log256(value) + 1);
        }
    }

    /**
     * @dev Converts a `uint256` to its ASCII `string` hexadecimal representation with fixed length.
     */
    function toHexString(uint256 value, uint256 length) internal pure returns (string memory) {
        uint256 localValue = value;
        bytes memory buffer = new bytes(2 * length + 2);
        buffer[0] = "0";
        buffer[1] = "x";
        for (uint256 i = 2 * length + 1; i > 1; --i) {
            buffer[i] = HEX_DIGITS[localValue & 0xf];
            localValue >>= 4;
        }
        if (localValue != 0) {
            revert StringsInsufficientHexLength(value, length);
        }
        return string(buffer);
    }

    /**
     * @dev Converts an `address` with fixed length of 20 bytes to its not checksummed ASCII `string` hexadecimal
     * representation.
     */
    function toHexString(address addr) internal pure returns (string memory) {
        return toHexString(uint256(uint160(addr)), ADDRESS_LENGTH);
    }

    /**
     * @dev Returns true if the two strings are equal.
     */
    function equal(string memory a, string memory b) internal pure returns (bool) {
        return bytes(a).length == bytes(b).length && keccak256(bytes(a)) == keccak256(bytes(b));
    }
}

// lib/openzeppelin-contracts/contracts/utils/cryptography/MessageHashUtils.sol

// OpenZeppelin Contracts (last updated v5.0.0) (utils/cryptography/MessageHashUtils.sol)

/**
 * @dev Signature message hash utilities for producing digests to be consumed by {ECDSA} recovery or signing.
 *
 * The library provides methods for generating a hash of a message that conforms to the
 * https://eips.ethereum.org/EIPS/eip-191[EIP 191] and https://eips.ethereum.org/EIPS/eip-712[EIP 712]
 * specifications.
 */
library MessageHashUtils {
    /**
     * @dev Returns the keccak256 digest of an EIP-191 signed data with version
     * `0x45` (`personal_sign` messages).
     *
     * The digest is calculated by prefixing a bytes32 `messageHash` with
     * `"\x19Ethereum Signed Message:\n32"` and hashing the result. It corresponds with the
     * hash signed when using the https://eth.wiki/json-rpc/API#eth_sign[`eth_sign`] JSON-RPC method.
     *
     * NOTE: The `messageHash` parameter is intended to be the result of hashing a raw message with
     * keccak256, although any bytes32 value can be safely used because the final digest will
     * be re-hashed.
     *
     * See {ECDSA-recover}.
     */
    function toEthSignedMessageHash(bytes32 messageHash) internal pure returns (bytes32 digest) {
        /// @solidity memory-safe-assembly
        assembly {
            mstore(0x00, "\x19Ethereum Signed Message:\n32") // 32 is the bytes-length of messageHash
            mstore(0x1c, messageHash) // 0x1c (28) is the length of the prefix
            digest := keccak256(0x00, 0x3c) // 0x3c is the length of the prefix (0x1c) + messageHash (0x20)
        }
    }

    /**
     * @dev Returns the keccak256 digest of an EIP-191 signed data with version
     * `0x45` (`personal_sign` messages).
     *
     * The digest is calculated by prefixing an arbitrary `message` with
     * `"\x19Ethereum Signed Message:\n" + len(message)` and hashing the result. It corresponds with the
     * hash signed when using the https://eth.wiki/json-rpc/API#eth_sign[`eth_sign`] JSON-RPC method.
     *
     * See {ECDSA-recover}.
     */
    function toEthSignedMessageHash(bytes memory message) internal pure returns (bytes32) {
        return
            keccak256(bytes.concat("\x19Ethereum Signed Message:\n", bytes(Strings.toString(message.length)), message));
    }

    /**
     * @dev Returns the keccak256 digest of an EIP-191 signed data with version
     * `0x00` (data with intended validator).
     *
     * The digest is calculated by prefixing an arbitrary `data` with `"\x19\x00"` and the intended
     * `validator` address. Then hashing the result.
     *
     * See {ECDSA-recover}.
     */
    function toDataWithIntendedValidatorHash(address validator, bytes memory data) internal pure returns (bytes32) {
        return keccak256(abi.encodePacked(hex"19_00", validator, data));
    }

    /**
     * @dev Returns the keccak256 digest of an EIP-712 typed data (EIP-191 version `0x01`).
     *
     * The digest is calculated from a `domainSeparator` and a `structHash`, by prefixing them with
     * `\x19\x01` and hashing the result. It corresponds to the hash signed by the
     * https://eips.ethereum.org/EIPS/eip-712[`eth_signTypedData`] JSON-RPC method as part of EIP-712.
     *
     * See {ECDSA-recover}.
     */
    function toTypedDataHash(bytes32 domainSeparator, bytes32 structHash) internal pure returns (bytes32 digest) {
        /// @solidity memory-safe-assembly
        assembly {
            let ptr := mload(0x40)
            mstore(ptr, hex"19_01")
            mstore(add(ptr, 0x02), domainSeparator)
            mstore(add(ptr, 0x22), structHash)
            digest := keccak256(ptr, 0x42)
        }
    }
}

// lib/openzeppelin-contracts/contracts/utils/cryptography/EIP712.sol

// OpenZeppelin Contracts (last updated v5.0.0) (utils/cryptography/EIP712.sol)

/**
 * @dev https://eips.ethereum.org/EIPS/eip-712[EIP 712] is a standard for hashing and signing of typed structured data.
 *
 * The encoding scheme specified in the EIP requires a domain separator and a hash of the typed structured data, whose
 * encoding is very generic and therefore its implementation in Solidity is not feasible, thus this contract
 * does not implement the encoding itself. Protocols need to implement the type-specific encoding they need in order to
 * produce the hash of their typed data using a combination of `abi.encode` and `keccak256`.
 *
 * This contract implements the EIP 712 domain separator ({_domainSeparatorV4}) that is used as part of the encoding
 * scheme, and the final step of the encoding to obtain the message digest that is then signed via ECDSA
 * ({_hashTypedDataV4}).
 *
 * The implementation of the domain separator was designed to be as efficient as possible while still properly updating
 * the chain id to protect against replay attacks on an eventual fork of the chain.
 *
 * NOTE: This contract implements the version of the encoding known as "v4", as implemented by the JSON RPC method
 * https://docs.metamask.io/guide/signing-data.html[`eth_signTypedDataV4` in MetaMask].
 *
 * NOTE: In the upgradeable version of this contract, the cached values will correspond to the address, and the domain
 * separator of the implementation contract. This will cause the {_domainSeparatorV4} function to always rebuild the
 * separator from the immutable values, which is cheaper than accessing a cached version in cold storage.
 *
 * @custom:oz-upgrades-unsafe-allow state-variable-immutable
 */
abstract contract EIP712 is IERC5267 {
    using ShortStrings for *;

    bytes32 private constant TYPE_HASH =
        keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)");

    // Cache the domain separator as an immutable value, but also store the chain id that it corresponds to, in order to
    // invalidate the cached domain separator if the chain id changes.
    bytes32 private immutable _cachedDomainSeparator;
    uint256 private immutable _cachedChainId;
    address private immutable _cachedThis;

    bytes32 private immutable _hashedName;
    bytes32 private immutable _hashedVersion;

    ShortString private immutable _name;
    ShortString private immutable _version;
    string private _nameFallback;
    string private _versionFallback;

    /**
     * @dev Initializes the domain separator and parameter caches.
     *
     * The meaning of `name` and `version` is specified in
     * https://eips.ethereum.org/EIPS/eip-712#definition-of-domainseparator[EIP 712]:
     *
     * - `name`: the user readable name of the signing domain, i.e. the name of the DApp or the protocol.
     * - `version`: the current major version of the signing domain.
     *
     * NOTE: These parameters cannot be changed except through a xref:learn::upgrading-smart-contracts.adoc[smart
     * contract upgrade].
     */
    constructor(string memory name, string memory version) {
        _name = name.toShortStringWithFallback(_nameFallback);
        _version = version.toShortStringWithFallback(_versionFallback);
        _hashedName = keccak256(bytes(name));
        _hashedVersion = keccak256(bytes(version));

        _cachedChainId = block.chainid;
        _cachedDomainSeparator = _buildDomainSeparator();
        _cachedThis = address(this);
    }

    /**
     * @dev Returns the domain separator for the current chain.
     */
    function _domainSeparatorV4() internal view returns (bytes32) {
        if (address(this) == _cachedThis && block.chainid == _cachedChainId) {
            return _cachedDomainSeparator;
        } else {
            return _buildDomainSeparator();
        }
    }

    function _buildDomainSeparator() private view returns (bytes32) {
        return keccak256(abi.encode(TYPE_HASH, _hashedName, _hashedVersion, block.chainid, address(this)));
    }

    /**
     * @dev Given an already https://eips.ethereum.org/EIPS/eip-712#definition-of-hashstruct[hashed struct], this
     * function returns the hash of the fully encoded EIP712 message for this domain.
     *
     * This hash can be used together with {ECDSA-recover} to obtain the signer of a message. For example:
     *
     * ```solidity
     * bytes32 digest = _hashTypedDataV4(keccak256(abi.encode(
     *     keccak256("Mail(address to,string contents)"),
     *     mailTo,
     *     keccak256(bytes(mailContents))
     * )));
     * address signer = ECDSA.recover(digest, signature);
     * ```
     */
    function _hashTypedDataV4(bytes32 structHash) internal view virtual returns (bytes32) {
        return MessageHashUtils.toTypedDataHash(_domainSeparatorV4(), structHash);
    }

    /**
     * @dev See {IERC-5267}.
     */
    function eip712Domain()
        public
        view
        virtual
        returns (
            bytes1 fields,
            string memory name,
            string memory version,
            uint256 chainId,
            address verifyingContract,
            bytes32 salt,
            uint256[] memory extensions
        )
    {
        return (
            hex"0f", // 01111
            _EIP712Name(),
            _EIP712Version(),
            block.chainid,
            address(this),
            bytes32(0),
            new uint256[](0)
        );
    }

    /**
     * @dev The name parameter for the EIP712 domain.
     *
     * NOTE: By default this function reads _name which is an immutable value.
     * It only reads from storage if necessary (in case the value is too large to fit in a ShortString).
     */
    // solhint-disable-next-line func-name-mixedcase
    function _EIP712Name() internal view returns (string memory) {
        return _name.toStringWithFallback(_nameFallback);
    }

    /**
     * @dev The version parameter for the EIP712 domain.
     *
     * NOTE: By default this function reads _version which is an immutable value.
     * It only reads from storage if necessary (in case the value is too large to fit in a ShortString).
     */
    // solhint-disable-next-line func-name-mixedcase
    function _EIP712Version() internal view returns (string memory) {
        return _version.toStringWithFallback(_versionFallback);
    }
}

// lib/fhenix-contracts/contracts/access/Permissioned.sol

/// @title Permissioned Access Control Contract
/// @notice Abstract contract that provides EIP-712 based signature verification for access control
/// @dev This contract should be inherited by other contracts to provide EIP-712 signature validated access control
abstract contract Permissioned is EIP712 {
    /// @notice Emitted when the signer is not the message sender
    error SignerNotMessageSender();

    /// @notice Emitted when the signer is not the specified owner
    error SignerNotOwner();

    /// @dev Constructor that initializes EIP712 domain separator with a name and version
    /// solhint-disable-next-line func-visibility, no-empty-blocks
    constructor() EIP712("Fhenix Permission", "1.0") {} 

    /// @notice Modifier that requires the provided signature to be signed by the message sender
    /// @param permission Data structure containing the public key and the signature to be verified
    modifier onlySender(Permission memory permission) {
        bytes32 digest = _hashTypedDataV4(keccak256(abi.encode(
            keccak256("Permissioned(bytes32 publicKey)"),
            permission.publicKey
        )));
        address signer = ECDSA.recover(digest, permission.signature);
        if (signer != msg.sender)
            revert SignerNotMessageSender();
        _;
    }

    /// @notice Modifier that requires the provided signature to be signed by a specific owner address
    /// @param permission Data structure containing the public key and the signature to be verified
    /// @param owner The expected owner of the public key to match against the recovered signer
    modifier onlyPermitted(Permission memory permission, address owner) {
        bytes32 digest = _hashTypedDataV4(keccak256(abi.encode(
            keccak256("Permissioned(bytes32 publicKey)"),
            permission.publicKey
        )));
        address signer = ECDSA.recover(digest, permission.signature);
        if (signer != owner)
            revert SignerNotOwner();
        _;
    }
}

/// @title Struct for holding signature information
/// @notice Used to pass both the public key and signature data within transactions
/// @dev Should be used with Signature-based modifiers for access control
struct Permission {
    bytes32 publicKey;
    bytes signature;
}

// src/CoreId.sol

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
