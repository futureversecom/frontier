//! Common types across runtimes, pallets, and/or client
#![cfg_attr(not(feature = "std"), no_std)]

pub use opaque::*;
pub use signature::*;
pub use types::*;

mod signature;
pub mod crypto {
	pub mod app_crypto {
		use sp_application_crypto::{app_crypto, ecdsa};
		use sp_runtime::KeyTypeId;
		app_crypto!(ecdsa, KeyTypeId(*b"test"));
	}
	sp_application_crypto::with_pair! {
		/// An eth bridge keypair using ecdsa as its crypto.
		pub type AuthorityPair = app_crypto::Pair;
	}
}

pub mod types {
	use crate::signature::EthereumSignature;
	use sp_runtime::traits::{IdentifyAccount, Verify};

	/// An index to a block.
	pub type BlockNumber = u32;

	/// Alias to 512-bit hash when used in the context of a transaction signature on the chain.
	pub type Signature = EthereumSignature;

	/// Some way of identifying an account on the chain. We intentionally make it equivalent
	/// to the public key of our transaction signing scheme.
	pub type AccountId = <<Signature as Verify>::Signer as IdentifyAccount>::AccountId;

	/// The chain address type
	pub type Address = AccountId;

	/// Balance of an account.
	pub type Balance = u128;

	/// Index of a transaction in the chain.
	pub type Index = u32;

	/// A hash of some data used by the chain.
	pub type Hash = sp_core::H256;

	/// Digest item type.
	pub type DigestItem = sp_runtime::generic::DigestItem;

	// Babe consensus authority.
	pub type BabeId = sp_consensus_babe::AuthorityId;

	// Id used for identifying assets.
	pub type AssetId = u32;

	pub type Timestamp = u64;
}

/// Opaque types. These are used by the CLI to instantiate machinery that don't need to know
/// the specifics of the runtime. They can then be made to be agnostic over specific formats
/// of data like extrinsics, allowing for them to continue syncing the network through upgrades
/// to even the core data structures.
pub mod opaque {
	use super::*;
	use sp_runtime::{generic, traits::BlakeTwo256};

	pub use sp_runtime::OpaqueExtrinsic as UncheckedExtrinsic;
	/// Opaque block header type.
	pub type Header = generic::Header<BlockNumber, BlakeTwo256>;
	/// Opaque block type.
	pub type Block = generic::Block<Header, UncheckedExtrinsic>;
	/// Opaque block identifier type.
	pub type BlockId = generic::BlockId<Block>;
}