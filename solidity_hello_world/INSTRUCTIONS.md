# How to Deploy HelloWorld.sol

## Option 1: Using Remix IDE (Easiest)

1.  **Open Remix:** Go to [https://remix.ethereum.org/](https://remix.ethereum.org/).
2.  **Create File:** In the "File Explorer" tab (left sidebar), create a new file named `HelloWorld.sol`.
3.  **Copy Code:** Paste the content of `HelloWorld.sol` from this directory into the Remix editor.
4.  **Compile:**
    *   Click the "Solidity Compiler" tab (3rd icon on the left).
    *   Ensure the "Compiler" version matches the pragma (e.g., 0.8.x).
    *   Click "Compile HelloWorld.sol".
5.  **Deploy:**
    *   Click the "Deploy & Run Transactions" tab (4th icon on the left).
    *   Under "Environment", choose "Remix VM (Cancun)" for a local testnet, or "Injected Provider - MetaMask" to deploy to a live network (Sepolia, Mainnet, etc.).
    *   Click the orange "Deploy" button.
6.  **Interact:**
    *   Once deployed, scroll down to "Deployed Contracts".
    *   Expand the `HelloWorld` contract.
    *   Click the `greet` button to see the "Hello World!" message.

## Option 2: Using Hardhat (Local Development Environment)

1.  **Initialize Project:**
    ```bash
    npm init -y
    npm install --save-dev hardhat
    npx hardhat init
    ```
    (Select "Create a JavaScript project")

2.  **Copy Contract:** Place `HelloWorld.sol` into the `contracts/` directory.

3.  **Compile:**
    ```bash
    npx hardhat compile
    ```

4.  **Deploy Script:** Create a script in `ignition/modules/HelloWorld.js` (or `scripts/deploy.js` for older Hardhat versions) to deploy the contract.

5.  **Run Deployment:**
    ```bash
    npx hardhat ignition deploy ignition/modules/HelloWorld.js --network localhost
    ```
