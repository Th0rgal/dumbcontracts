// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";

contract ERC721Model {
    address private _owner;
    uint256 private _totalSupply;
    uint256 private _nextTokenId;

    mapping(address => uint256) private _balances;
    mapping(uint256 => address) private _owners;
    mapping(uint256 => address) private _tokenApprovals;
    mapping(address => mapping(address => bool)) private _operatorApprovals;

    constructor(address initialOwner) {
        _owner = initialOwner;
        _totalSupply = 0;
        _nextTokenId = 0;
    }

    function owner() external view returns (address) {
        return _owner;
    }

    function totalSupply() external view returns (uint256) {
        return _totalSupply;
    }

    function nextTokenId() external view returns (uint256) {
        return _nextTokenId;
    }

    function balanceOf(address addr) external view returns (uint256) {
        return _balances[addr];
    }

    function ownerOf(uint256 tokenId) public view returns (address) {
        address tokenOwner = _owners[tokenId];
        require(tokenOwner != address(0), "Token does not exist");
        return tokenOwner;
    }

    function getApproved(uint256 tokenId) external view returns (address) {
        require(_owners[tokenId] != address(0), "Token does not exist");
        return _tokenApprovals[tokenId];
    }

    function isApprovedForAll(address ownerAddr, address operator) external view returns (bool) {
        return _operatorApprovals[ownerAddr][operator];
    }

    function setApprovalForAll(address operator, bool approved) external {
        _operatorApprovals[msg.sender][operator] = approved;
    }

    function approve(address approved, uint256 tokenId) external {
        address tokenOwner = ownerOf(tokenId);
        require(msg.sender == tokenOwner, "Not token owner");
        _tokenApprovals[tokenId] = approved;
    }

    function mint(address to) external returns (uint256) {
        require(msg.sender == _owner, "Caller is not the owner");
        require(to != address(0), "Invalid recipient");

        uint256 tokenId = _nextTokenId;
        require(_owners[tokenId] == address(0), "Token already minted");

        _owners[tokenId] = to;
        _balances[to] += 1;
        _totalSupply += 1;
        _nextTokenId = tokenId + 1;
        return tokenId;
    }

    function transferFrom(address fromAddr, address to, uint256 tokenId) external {
        require(to != address(0), "Invalid recipient");
        address tokenOwner = ownerOf(tokenId);
        require(tokenOwner == fromAddr, "From is not owner");

        bool authorized = msg.sender == fromAddr
            || _tokenApprovals[tokenId] == msg.sender
            || _operatorApprovals[fromAddr][msg.sender];
        require(authorized, "Not authorized");

        if (fromAddr != to) {
            require(_balances[fromAddr] >= 1, "Insufficient balance");
            _balances[fromAddr] -= 1;
            _balances[to] += 1;
        }

        _owners[tokenId] = to;
        _tokenApprovals[tokenId] = address(0);
    }
}

contract PropertyERC721Test is Test {
    ERC721Model internal nft;

    address internal constant OWNER = address(0xA11CE);
    address internal constant ALICE = address(0xA1);
    address internal constant BOB = address(0xB0B);
    address internal constant CHARLIE = address(0xC4A12);
    address internal constant OPERATOR = address(0x0B5);

    function setUp() public {
        nft = new ERC721Model(OWNER);
    }

    function _mintAsOwner(address to) internal returns (uint256 tokenId) {
        vm.prank(OWNER);
        tokenId = nft.mint(to);
    }

    /// Property: constructor_meets_spec
    function testProperty_Constructor_SetsOwner() public view {
        assertEq(nft.owner(), OWNER, "owner mismatch");
    }

    /// Property: constructor_meets_spec
    function testProperty_Constructor_InitializesCountersToZero() public view {
        assertEq(nft.totalSupply(), 0, "initial supply must be zero");
        assertEq(nft.nextTokenId(), 0, "initial next token must be zero");
    }

    /// Property: balanceOf_meets_spec
    function testProperty_Mint_AssignsOwnershipCorrectly(address recipient) public {
        vm.assume(recipient != address(0));
        uint256 tokenId = _mintAsOwner(recipient);
        assertEq(nft.ownerOf(tokenId), recipient, "ownerOf mismatch after mint");
    }

    /// Property: balanceOf_meets_spec
    function testProperty_Mint_IncreasesRecipientBalance(address recipient) public {
        vm.assume(recipient != address(0));

        uint256 beforeBal = nft.balanceOf(recipient);
        _mintAsOwner(recipient);

        assertEq(nft.balanceOf(recipient), beforeBal + 1, "recipient balance did not increment");
    }

    /// Property: constructor_meets_spec
    function testProperty_Mint_IncreasesTotalSupply(address recipient) public {
        vm.assume(recipient != address(0));

        uint256 before = nft.totalSupply();
        _mintAsOwner(recipient);

        assertEq(nft.totalSupply(), before + 1, "supply did not increment");
    }

    /// Property: constructor_meets_spec
    function testProperty_Mint_UsesSequentialTokenIds(address recipientA, address recipientB) public {
        vm.assume(recipientA != address(0));
        vm.assume(recipientB != address(0));

        uint256 t0 = _mintAsOwner(recipientA);
        uint256 t1 = _mintAsOwner(recipientB);

        assertEq(t0, 0, "first token id must be 0");
        assertEq(t1, 1, "second token id must be 1");
        assertEq(nft.nextTokenId(), 2, "next token id mismatch");
    }

    /// Property: constructor_meets_spec
    function testProperty_Mint_RevertsWhenNotOwner(address recipient) public {
        vm.assume(recipient != address(0));
        vm.prank(ALICE);
        vm.expectRevert(bytes("Caller is not the owner"));
        nft.mint(recipient);
    }

    /// Property: ownerOf_meets_spec
    function testProperty_TransferFrom_UpdatesOwnership() public {
        uint256 tokenId = _mintAsOwner(ALICE);

        vm.prank(ALICE);
        nft.transferFrom(ALICE, BOB, tokenId);

        assertEq(nft.ownerOf(tokenId), BOB, "ownership not transferred");
    }

    /// Property: balanceOf_meets_spec
    function testProperty_TransferFrom_UpdatesBalances() public {
        uint256 tokenId = _mintAsOwner(ALICE);
        uint256 aliceBefore = nft.balanceOf(ALICE);
        uint256 bobBefore = nft.balanceOf(BOB);

        vm.prank(ALICE);
        nft.transferFrom(ALICE, BOB, tokenId);

        assertEq(nft.balanceOf(ALICE), aliceBefore - 1, "sender balance mismatch");
        assertEq(nft.balanceOf(BOB), bobBefore + 1, "recipient balance mismatch");
    }

    /// Property: getApproved_meets_spec
    function testProperty_Approve_ThenTransferFrom_ByApprovedAddress() public {
        uint256 tokenId = _mintAsOwner(ALICE);

        vm.prank(ALICE);
        nft.approve(BOB, tokenId);

        vm.prank(BOB);
        nft.transferFrom(ALICE, CHARLIE, tokenId);

        assertEq(nft.ownerOf(tokenId), CHARLIE, "approved transfer failed");
    }

    /// Property: getApproved_meets_spec
    /// Property: getApproved_preserves_state
    function testProperty_TransferFrom_ClearsSingleTokenApproval() public {
        uint256 tokenId = _mintAsOwner(ALICE);

        vm.prank(ALICE);
        nft.approve(BOB, tokenId);

        vm.prank(BOB);
        nft.transferFrom(ALICE, CHARLIE, tokenId);

        assertEq(nft.getApproved(tokenId), address(0), "approval was not cleared");
    }

    /// Property: isApprovedForAll_meets_spec
    /// Property: setApprovalForAll_meets_spec
    function testProperty_SetApprovalForAll_EnablesOperatorTransfer() public {
        uint256 tokenId = _mintAsOwner(ALICE);

        vm.prank(ALICE);
        nft.setApprovalForAll(OPERATOR, true);

        vm.prank(OPERATOR);
        nft.transferFrom(ALICE, BOB, tokenId);

        assertEq(nft.ownerOf(tokenId), BOB, "operator transfer failed");
    }

    /// Property: setApprovalForAll_is_balance_neutral_holds
    function testProperty_SetApprovalForAll_PreservesBalances() public {
        _mintAsOwner(ALICE);

        uint256 aliceBefore = nft.balanceOf(ALICE);
        uint256 bobBefore = nft.balanceOf(BOB);
        uint256 supplyBefore = nft.totalSupply();

        vm.prank(ALICE);
        nft.setApprovalForAll(OPERATOR, true);

        assertEq(nft.balanceOf(ALICE), aliceBefore, "owner balance changed");
        assertEq(nft.balanceOf(BOB), bobBefore, "other balance changed");
        assertEq(nft.totalSupply(), supplyBefore, "supply changed");
    }

    /// Property: ownerOf_meets_spec
    function testProperty_TransferFrom_RevertsWhenUnauthorized() public {
        uint256 tokenId = _mintAsOwner(ALICE);

        vm.prank(CHARLIE);
        vm.expectRevert(bytes("Not authorized"));
        nft.transferFrom(ALICE, BOB, tokenId);
    }

    /// Property: ownerOf_meets_spec
    function testProperty_TransferFrom_RevertsWhenFromIsNotOwner() public {
        uint256 tokenId = _mintAsOwner(ALICE);

        vm.prank(ALICE);
        vm.expectRevert(bytes("From is not owner"));
        nft.transferFrom(BOB, CHARLIE, tokenId);
    }

    /// Property: ownerOf_meets_spec
    function testProperty_TransferFrom_RevertsForZeroRecipient() public {
        uint256 tokenId = _mintAsOwner(ALICE);

        vm.prank(ALICE);
        vm.expectRevert(bytes("Invalid recipient"));
        nft.transferFrom(ALICE, address(0), tokenId);
    }

    /// Property: ownerOf_preserves_state
    function testProperty_OwnerOf_ReadOnlyViewPreservesSupply() public {
        uint256 tokenId = _mintAsOwner(ALICE);
        uint256 supplyBefore = nft.totalSupply();

        nft.ownerOf(tokenId);

        assertEq(nft.totalSupply(), supplyBefore, "ownerOf changed totalSupply");
    }

    /// Property: isApprovedForAll_preserves_state
    function testProperty_IsApprovedForAll_ReadOnlyViewPreservesBalances() public {
        _mintAsOwner(ALICE);
        uint256 aliceBefore = nft.balanceOf(ALICE);

        nft.isApprovedForAll(ALICE, OPERATOR);

        assertEq(nft.balanceOf(ALICE), aliceBefore, "isApprovedForAll changed balances");
    }

    /// Property: balanceOf_preserves_state
    function testProperty_BalanceOf_ReadOnlyViewPreservesOwnership() public {
        uint256 tokenId = _mintAsOwner(ALICE);
        address ownerBefore = nft.ownerOf(tokenId);

        nft.balanceOf(ALICE);

        assertEq(nft.ownerOf(tokenId), ownerBefore, "balanceOf changed ownership");
    }
}
