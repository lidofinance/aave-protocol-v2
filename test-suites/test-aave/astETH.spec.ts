import BigNumber from 'bignumber.js';

import { TestEnv, makeSuite } from './helpers/make-suite';
import { MAX_UINT_AMOUNT, APPROVAL_AMOUNT_LENDING_POOL, oneRay } from '../../helpers/constants';
import { convertToCurrencyDecimals, getContract } from '../../helpers/contracts-helpers';
// import {ethers} from 'ethers';
import { ProtocolErrors, eContractid, RateMode } from '../../helpers/types';
import { VariableDebtToken } from '../../types/VariableDebtToken';
import { StableDebtToken } from '../../types/StableDebtToken';
import { AStETH } from '../../types/AStETH';
import { VariableDebtStETH } from '../../types/VariableDebtStETH';
import {
  getAStETH,
  getVariableDebtStETH,
  getLendingRateOracle,
  getReserveLogic,
} from '../../helpers/contracts-getters';
import { BigNumberish, ethers } from 'ethers';
import { LendingRateOracle } from '../../types/LendingRateOracle';
import { ILendingRateOracle } from '../../types/ILendingRateOracle';
import {
  calcExpectedVariableDebtTokenBalance,
  calcExpectedStableDebtTokenBalance,
  calcExpectedATokenBalance,
} from './helpers/utils/calculations';
import { getTxCostAndTimestamp } from './helpers/actions';
import {
  DRE,
  waitForTx,
  advanceTimeAndBlock,
  evmSnapshot,
  evmRevert,
} from '../../helpers/misc-utils';
import { getReserveData, getUserData } from './helpers/utils/helpers';
const { expect } = require('chai');

let lenderA,
  lenderB,
  lenderC,
  admin,
  borrowerA,
  borrowerB,
  lenderAAddress,
  lenderBAddress,
  lenderCAddress,
  adminAddress,
  borrowerAAddress,
  borrowerBAddress,
  evmSnapshotId,
  reserveData,
  astETH: AStETH,
  debtToken: VariableDebtStETH,
  treasuryAddress;

async function rebase(pool, steth, perc) {
  const currentSupply = new BigNumber((await steth.totalSupply()).toString());
  const supplyDelta = currentSupply.multipliedBy(perc);

  // tiny deposit to get the pool in sync
  //   await steth.connect(admin.signer).approve(pool.address, await fxtPt(steth, '1'));
  //   await pool
  //     .connect(admin.signer)
  //     .deposit(steth.address, await fxtPt(steth, '0.000001'), adminAddress, '0');
  await steth.rebase(supplyDelta.toString(10));
  //   await pool
  //     .connect(admin.signer)
  //     .deposit(steth.address, await fxtPt(steth, '0.000001'), adminAddress, '0');
}

function fxtPt(t, amt) {
  return convertToCurrencyDecimals(t.address, amt);
}

async function check(amt, cmpAmt, token, tolarance) {
  const t = new BigNumber(tolarance).multipliedBy(10 ** (await token.decimals())).toString();
  expect(amt).to.be.bignumber.gte(cmpAmt.sub(t)).lte(cmpAmt.add(t));
}

// tolarance 1 StETH cent ~= 0.01 StETH
async function checkBal(token, addr, amt, tolarance = 0.01) {
  return check(await token.balanceOf(addr), await fxtPt(token, amt), token, tolarance);
}

async function checkScaledBal(token, addr, amt, tolarance = 0.01) {
  return check(await token.scaledBalanceOf(addr), await fxtPt(token, amt), token, tolarance);
}

async function checkSupply(token, amt, tolarance = 0.01) {
  return check(await token.totalSupply(), await fxtPt(token, amt), token, tolarance);
}

makeSuite('StETH aToken', (testEnv: TestEnv) => {
  beforeEach(async () => {
    evmSnapshotId = await evmSnapshot();

    const { users, stETH, deployer, helpersContract, pool } = testEnv;

    lenderA = users[1];
    lenderB = users[2];
    lenderC = users[3];
    borrowerA = users[4];
    borrowerB = users[5];
    admin = users[6];

    lenderAAddress = lenderA.address;
    lenderBAddress = lenderB.address;
    lenderCAddress = lenderC.address;
    borrowerAAddress = borrowerA.address;
    borrowerBAddress = borrowerB.address;
    adminAddress = admin.address;

    reserveData = await pool.getReserveData(stETH.address);
    astETH = await getAStETH(reserveData.aTokenAddress);
    debtToken = await getVariableDebtStETH(reserveData.variableDebtTokenAddress);
    treasuryAddress = await astETH.RESERVE_TREASURY_ADDRESS();

    await astETH.initializeDebtToken();

    await stETH.connect(deployer.signer).mint(deployer.address, await fxtPt(stETH, '1000000000'));
    await stETH.connect(deployer.signer).transfer(lenderAAddress, await fxtPt(stETH, '100000'));
    await stETH.connect(deployer.signer).transfer(lenderBAddress, await fxtPt(stETH, '100000'));
    await stETH.connect(deployer.signer).transfer(lenderCAddress, await fxtPt(stETH, '100000'));
    await stETH.connect(deployer.signer).transfer(adminAddress, await fxtPt(stETH, '1000'));
  });

  afterEach(async () => {
    await evmRevert(evmSnapshotId);
  });

  describe('steth rebasing', () => {
    describe('positive rebase', function () {
      it('should update total supply correctly', async () => {
        const { pool, stETH } = testEnv;

        const perc = 0.1;
        const currentSupply = new BigNumber((await steth.totalSupply()).toString());
        await rebase(pool, stETH, perc);
        const afterBalance = currentSupply.add(supplyDelta);
        const newTotalSupply = await steth.totalSupply();

        expect(newTotalSupply.toString()).to.be.equal(afterBalance.toString());
      });
    });
    describe('negative rebase', function () {
      it('should update total supply correctly', async () => {});
    });
  });

  describe('user Transfer', () => {
    describe('when lenderA deposits 1000 StETH, transfers all to himself', function () {
      it('should update balances correctly', async () => {
        const { pool, stETH } = testEnv;

        await stETH.connect(lenderA.signer).approve(pool.address, await fxtPt(stETH, '1000'));
        await pool
          .connect(lenderA.signer)
          .deposit(stETH.address, await fxtPt(stETH, '1000'), lenderAAddress, '0');

        const beforeBalance = await astETH.scaledBalanceOf(lenderAAddress);
        await astETH
          .connect(lenderA.signer)
          .transfer(lenderAAddress, await astETH.balanceOf(lenderAAddress));
        const afterBalance = await astETH.scaledBalanceOf(lenderAAddress);

        expect(beforeBalance.toString()).to.be.equal(afterBalance.toString());
      });
    });

    describe('when lenderA deposits 1000 StETH, transfers more than he has', function () {
      it('should update balances correctly', async () => {
        const { pool, stETH } = testEnv;

        await stETH.connect(lenderA.signer).approve(pool.address, await fxtPt(stETH, '1000'));
        await pool
          .connect(lenderA.signer)
          .deposit(stETH.address, await fxtPt(stETH, '1000'), lenderAAddress, '0');

        await expect(
          astETH.connect(lenderA.signer).transfer(lenderAAddress, await fxtPt(stETH, '1001'))
        ).to.be.revertedWith('transfer amount exceeds balance');
      });
    });

    describe('when borrowed amount > 0', function () {
      describe('when lenderA deposits 1000 StETH, transfers all to himself', function () {
        it('should update balances correctly', async () => {
          const { pool, dai, stETH, aDai } = testEnv;

          await stETH.connect(lenderA.signer).approve(pool.address, await fxtPt(stETH, '1000'));
          await pool
            .connect(lenderA.signer)
            .deposit(stETH.address, await fxtPt(stETH, '1000'), lenderAAddress, '0');

          await dai.mint(await fxtPt(dai, '2000'));
          await dai.transfer(borrowerAAddress, await fxtPt(dai, '2000'));
          await dai.connect(borrowerA.signer).approve(pool.address, await fxtPt(dai, '2000'));
          await pool
            .connect(borrowerA.signer)
            .deposit(dai.address, await fxtPt(dai, '2000'), borrowerAAddress, '0');

          await pool
            .connect(borrowerA.signer)
            .borrow(
              stETH.address,
              await fxtPt(stETH, '250'),
              RateMode.Variable,
              '0',
              borrowerAAddress
            );

          const beforeBalance = await astETH.scaledBalanceOf(lenderAAddress);
          await astETH
            .connect(lenderA.signer)
            .transfer(lenderAAddress, await astETH.balanceOf(lenderAAddress));
          const afterBalance = await astETH.scaledBalanceOf(lenderAAddress);

          expect(beforeBalance.toString()).to.be.equal(afterBalance.toString());
        });
      });

      describe('when lenderA deposits 1000 StETH, transfers more than he has', function () {
        it('should update balances correctly', async () => {
          const { pool, dai, stETH, aDai } = testEnv;

          await stETH.connect(lenderA.signer).approve(pool.address, await fxtPt(stETH, '1000'));
          await pool
            .connect(lenderA.signer)
            .deposit(stETH.address, await fxtPt(stETH, '1000'), lenderAAddress, '0');

          await dai.mint(await fxtPt(dai, '2000'));
          await dai.transfer(borrowerAAddress, await fxtPt(dai, '2000'));
          await dai.connect(borrowerA.signer).approve(pool.address, await fxtPt(dai, '2000'));
          await pool
            .connect(borrowerA.signer)
            .deposit(dai.address, await fxtPt(dai, '2000'), borrowerAAddress, '0');

          await pool
            .connect(borrowerA.signer)
            .borrow(
              stETH.address,
              await fxtPt(stETH, '250'),
              RateMode.Variable,
              '0',
              borrowerAAddress
            );

          await expect(
            astETH.connect(lenderA.signer).transfer(lenderAAddress, await fxtPt(stETH, '1001'))
          ).to.be.revertedWith('transfer amount exceeds balance');
        });
      });
    });
  });

  describe('user deposit', function () {
    describe('first deposit', function () {
      it('should mint correct number of astETH tokens', async () => {
        const { pool, stETH, aDai, helpersContract } = testEnv;

        await checkBal(stETH, lenderAAddress, '100000');
        await checkBal(astETH, lenderAAddress, '0');
        await checkBal(stETH, reserveData.aTokenAddress, '0');
        await checkSupply(astETH, '0');

        await stETH.connect(lenderA.signer).approve(pool.address, await fxtPt(stETH, '1000'));
        await pool
          .connect(lenderA.signer)
          .deposit(stETH.address, await fxtPt(stETH, '1000'), lenderAAddress, '0');

        expect(await astETH.balanceOf(lenderAAddress)).to.eq(await fxtPt(stETH, '1000'));

        await checkBal(stETH, lenderAAddress, '99000');
        await checkBal(astETH, lenderAAddress, '1000');
        await checkBal(stETH, reserveData.aTokenAddress, '1000');
        await checkSupply(astETH, '1000');
      });

      it('should update balances after positive rebase', async () => {
        const { pool, stETH } = testEnv;

        await stETH.connect(lenderA.signer).approve(pool.address, await fxtPt(stETH, '1000'));
        await pool
          .connect(lenderA.signer)
          .deposit(stETH.address, await fxtPt(stETH, '1000'), lenderAAddress, '0');

        await checkBal(stETH, lenderAAddress, '99000');
        await checkBal(astETH, lenderAAddress, '1000');
        await checkBal(stETH, reserveData.aTokenAddress, '1000');
        await checkSupply(astETH, '1000');

        await rebase(pool, stETH, 0.1); // + 10%

        expect(await astETH.balanceOf(lenderAAddress)).to.eq(await fxtPt(stETH, '1100'));

        await checkBal(stETH, lenderAAddress, '108900');
        await checkBal(astETH, lenderAAddress, '1100');
        await checkBal(stETH, reserveData.aTokenAddress, '1100');
        await checkSupply(astETH, '1100');
      });

      it('should update balances after negative rebase', async () => {
        const { pool, stETH } = testEnv;

        await stETH.connect(lenderA.signer).approve(pool.address, await fxtPt(stETH, '1000'));
        await pool
          .connect(lenderA.signer)
          .deposit(stETH.address, await fxtPt(stETH, '1000'), lenderAAddress, '0');

        await checkBal(stETH, lenderAAddress, '99000');
        await checkBal(astETH, lenderAAddress, '1000');
        await checkBal(stETH, reserveData.aTokenAddress, '1000');
        await checkSupply(astETH, '1000');

        await rebase(pool, stETH, -0.1); // - 10%

        expect(await astETH.balanceOf(lenderAAddress)).to.eq(await fxtPt(stETH, '900'));

        await checkBal(stETH, lenderAAddress, '89100');
        await checkBal(astETH, lenderAAddress, '900');
        await checkBal(stETH, reserveData.aTokenAddress, '900');
        await checkSupply(astETH, '900');
      });

      it('should update balances after neutral rebase', async () => {
        const { pool, stETH } = testEnv;

        await stETH.connect(lenderA.signer).approve(pool.address, await fxtPt(stETH, '1000'));
        await pool
          .connect(lenderA.signer)
          .deposit(stETH.address, await fxtPt(stETH, '1000'), lenderAAddress, '0');

        await checkBal(stETH, lenderAAddress, '99000');
        await checkBal(astETH, lenderAAddress, '1000');
        await checkBal(stETH, reserveData.aTokenAddress, '1000');
        await checkSupply(astETH, '1000');

        await rebase(pool, stETH, 0);

        expect(await astETH.balanceOf(lenderAAddress)).to.eq(await fxtPt(stETH, '1000'));

        await checkBal(stETH, lenderAAddress, '99000');
        await checkBal(astETH, lenderAAddress, '1000');
        await checkBal(stETH, reserveData.aTokenAddress, '1000');
        await checkSupply(astETH, '1000');
      });
    });

    describe('lone user', function () {
      it('should mint correct number of astETH tokens', async () => {
        const { pool, stETH } = testEnv;

        await stETH.connect(lenderA.signer).approve(pool.address, await fxtPt(stETH, '11000'));
        await pool
          .connect(lenderA.signer)
          .deposit(stETH.address, await fxtPt(stETH, '1000'), lenderAAddress, '0');

        await checkBal(stETH, lenderAAddress, '99000');
        await checkBal(astETH, lenderAAddress, '1000');
        await checkBal(stETH, reserveData.aTokenAddress, '1000');
        await checkSupply(astETH, '1000');

        await pool
          .connect(lenderA.signer)
          .deposit(stETH.address, await fxtPt(stETH, '10000'), lenderAAddress, '0');

        expect(await astETH.balanceOf(lenderAAddress)).to.eq(await fxtPt(stETH, '11000'));

        await checkBal(stETH, lenderAAddress, '89000');
        await checkBal(astETH, lenderAAddress, '11000');
        await checkBal(stETH, reserveData.aTokenAddress, '11000');
        await checkSupply(astETH, '11000');
      });

      it('should update balances after positive rebase', async () => {
        const { pool, stETH } = testEnv;

        await stETH.connect(lenderA.signer).approve(pool.address, await fxtPt(stETH, '11000'));
        await pool
          .connect(lenderA.signer)
          .deposit(stETH.address, await fxtPt(stETH, '1000'), lenderAAddress, '0');
        await pool
          .connect(lenderA.signer)
          .deposit(stETH.address, await fxtPt(stETH, '10000'), lenderAAddress, '0');

        await checkBal(stETH, lenderAAddress, '89000');
        await checkBal(astETH, lenderAAddress, '11000');
        await checkBal(stETH, reserveData.aTokenAddress, '11000');
        await checkSupply(astETH, '11000');

        await rebase(pool, stETH, +0.1);

        expect(await astETH.balanceOf(lenderAAddress)).to.eq(await fxtPt(stETH, '12100'));

        await checkBal(stETH, lenderAAddress, '97900');
        await checkBal(astETH, lenderAAddress, '12100');
        await checkBal(stETH, reserveData.aTokenAddress, '12100');
        await checkSupply(astETH, '12100');
      });

      it('should update balances after negative rebase', async () => {
        const { pool, stETH } = testEnv;

        await stETH.connect(lenderA.signer).approve(pool.address, await fxtPt(stETH, '11000'));
        await pool
          .connect(lenderA.signer)
          .deposit(stETH.address, await fxtPt(stETH, '1000'), lenderAAddress, '0');
        await pool
          .connect(lenderA.signer)
          .deposit(stETH.address, await fxtPt(stETH, '10000'), lenderAAddress, '0');

        await checkBal(stETH, lenderAAddress, '89000');
        await checkBal(astETH, lenderAAddress, '11000');
        await checkBal(stETH, reserveData.aTokenAddress, '11000');
        await checkSupply(astETH, '11000');

        await rebase(pool, stETH, -0.1);

        expect(await astETH.balanceOf(lenderAAddress)).to.eq(await fxtPt(stETH, '9900'));

        await checkBal(stETH, lenderAAddress, '80100');
        await checkBal(astETH, lenderAAddress, '9900');
        await checkBal(stETH, reserveData.aTokenAddress, '9900');
        await checkSupply(astETH, '9900');
      });
    });

    describe('many users', function () {
      it('should mint correct number of astETH tokens', async () => {
        const { pool, stETH } = testEnv;

        await stETH.connect(lenderA.signer).approve(pool.address, await fxtPt(stETH, '33000'));
        await stETH.connect(lenderB.signer).approve(pool.address, await fxtPt(stETH, '5000'));
        await stETH.connect(lenderC.signer).approve(pool.address, await fxtPt(stETH, '350'));

        await pool
          .connect(lenderA.signer)
          .deposit(stETH.address, await fxtPt(stETH, '30000'), lenderAAddress, '0');
        await pool
          .connect(lenderB.signer)
          .deposit(stETH.address, await fxtPt(stETH, '5000'), lenderBAddress, '0');
        await pool
          .connect(lenderC.signer)
          .deposit(stETH.address, await fxtPt(stETH, '350'), lenderCAddress, '0');

        await checkBal(stETH, lenderAAddress, '70000');
        await checkBal(stETH, lenderBAddress, '95000');
        await checkBal(stETH, lenderCAddress, '99650');
        await checkBal(astETH, lenderAAddress, '30000');
        await checkBal(astETH, lenderBAddress, '5000');
        await checkBal(astETH, lenderCAddress, '350');
        await checkBal(stETH, reserveData.aTokenAddress, '35350');
        await checkSupply(astETH, '35350');

        await pool
          .connect(lenderA.signer)
          .deposit(stETH.address, await fxtPt(stETH, '3000'), lenderAAddress, '0');

        expect(await astETH.balanceOf(lenderAAddress)).to.eq(await fxtPt(stETH, '33000'));

        await checkBal(stETH, lenderAAddress, '67000');
        await checkBal(stETH, lenderBAddress, '95000');
        await checkBal(stETH, lenderCAddress, '99650');
        await checkBal(astETH, lenderAAddress, '33000');
        await checkBal(astETH, lenderBAddress, '5000');
        await checkBal(astETH, lenderCAddress, '350');
        await checkBal(stETH, reserveData.aTokenAddress, '38350');
        await checkSupply(astETH, '38350');
      });

      it('should update balances after positive rebase', async () => {
        const { pool, stETH } = testEnv;

        await stETH.connect(lenderA.signer).approve(pool.address, await fxtPt(stETH, '33000'));
        await stETH.connect(lenderB.signer).approve(pool.address, await fxtPt(stETH, '5000'));
        await stETH.connect(lenderC.signer).approve(pool.address, await fxtPt(stETH, '350'));

        await pool
          .connect(lenderA.signer)
          .deposit(stETH.address, await fxtPt(stETH, '30000'), lenderAAddress, '0');
        await pool
          .connect(lenderB.signer)
          .deposit(stETH.address, await fxtPt(stETH, '5000'), lenderBAddress, '0');
        await pool
          .connect(lenderC.signer)
          .deposit(stETH.address, await fxtPt(stETH, '350'), lenderCAddress, '0');

        await pool
          .connect(lenderA.signer)
          .deposit(stETH.address, await fxtPt(stETH, '3000'), lenderAAddress, '0');

        expect(await astETH.balanceOf(lenderAAddress)).to.eq(await fxtPt(stETH, '33000'));

        await checkBal(stETH, lenderAAddress, '67000');
        await checkBal(stETH, lenderBAddress, '95000');
        await checkBal(stETH, lenderCAddress, '99650');
        await checkBal(astETH, lenderAAddress, '33000');
        await checkBal(astETH, lenderBAddress, '5000');
        await checkBal(astETH, lenderCAddress, '350');
        await checkBal(stETH, reserveData.aTokenAddress, '38350');
        await checkSupply(astETH, '38350');

        await rebase(pool, stETH, +0.1);

        expect(await astETH.balanceOf(lenderAAddress)).to.eq(await fxtPt(stETH, '36300'));

        await checkBal(stETH, lenderAAddress, '73700');
        await checkBal(stETH, lenderBAddress, '104500');
        await checkBal(stETH, lenderCAddress, '109615');
        await checkBal(astETH, lenderAAddress, '36300');
        await checkBal(astETH, lenderBAddress, '5500');
        await checkBal(astETH, lenderCAddress, '385');
        await checkBal(stETH, reserveData.aTokenAddress, '42185');
        await checkSupply(astETH, '42185');
      });

      it('should update balances after negative rebase', async () => {
        const { pool, stETH } = testEnv;

        await stETH.connect(lenderA.signer).approve(pool.address, await fxtPt(stETH, '33000'));
        await stETH.connect(lenderB.signer).approve(pool.address, await fxtPt(stETH, '5000'));
        await stETH.connect(lenderC.signer).approve(pool.address, await fxtPt(stETH, '350'));

        await pool
          .connect(lenderA.signer)
          .deposit(stETH.address, await fxtPt(stETH, '30000'), lenderAAddress, '0');
        await pool
          .connect(lenderB.signer)
          .deposit(stETH.address, await fxtPt(stETH, '5000'), lenderBAddress, '0');
        await pool
          .connect(lenderC.signer)
          .deposit(stETH.address, await fxtPt(stETH, '350'), lenderCAddress, '0');

        await pool
          .connect(lenderA.signer)
          .deposit(stETH.address, await fxtPt(stETH, '3000'), lenderAAddress, '0');

        expect(await astETH.balanceOf(lenderAAddress)).to.eq(await fxtPt(stETH, '33000'));

        await checkBal(stETH, lenderAAddress, '67000');
        await checkBal(stETH, lenderBAddress, '95000');
        await checkBal(stETH, lenderCAddress, '99650');
        await checkBal(astETH, lenderAAddress, '33000');
        await checkBal(astETH, lenderBAddress, '5000');
        await checkBal(astETH, lenderCAddress, '350');
        await checkBal(stETH, reserveData.aTokenAddress, '38350');
        await checkSupply(astETH, '38350');

        await rebase(pool, stETH, -0.1);

        expect(await astETH.balanceOf(lenderAAddress)).to.eq(await fxtPt(stETH, '29700'));

        await checkBal(stETH, lenderAAddress, '60300');
        await checkBal(stETH, lenderBAddress, '85500');
        await checkBal(stETH, lenderCAddress, '89685');
        await checkBal(astETH, lenderAAddress, '29700');
        await checkBal(astETH, lenderBAddress, '4500');
        await checkBal(astETH, lenderCAddress, '315');
        await checkBal(stETH, reserveData.aTokenAddress, '34515');
        await checkSupply(astETH, '34515');
      });
    });

    describe('v large deposit', function () {
      it('should mint correct number of astETH tokens', async () => {
        const { deployer, pool, stETH } = testEnv;

        await stETH.connect(deployer.signer).transfer(lenderAAddress, await fxtPt(stETH, '100000'));
        await rebase(pool, stETH, 9999999);
        await checkSupply(stETH, '500000000000000'); // 500T

        await stETH
          .connect(lenderA.signer)
          .approve(pool.address, await fxtPt(stETH, '1000000000000')); // 1T
        await stETH
          .connect(lenderB.signer)
          .approve(pool.address, await fxtPt(stETH, '500000000000')); // 0.5T
        await stETH
          .connect(lenderC.signer)
          .approve(pool.address, await fxtPt(stETH, '500000000000')); // 0.5T
        await pool
          .connect(lenderA.signer)
          .deposit(stETH.address, await fxtPt(stETH, '1000000000000'), lenderAAddress, '0');
        await pool
          .connect(lenderB.signer)
          .deposit(stETH.address, await fxtPt(stETH, '500000000000'), lenderBAddress, '0');
        await pool
          .connect(lenderC.signer)
          .deposit(stETH.address, await fxtPt(stETH, '500000000000'), lenderCAddress, '0');

        await checkBal(stETH, lenderAAddress, '1000000000000', 10000);
        await checkBal(stETH, lenderBAddress, '500000000000', 10000);
        await checkBal(stETH, lenderCAddress, '500000000000', 10000);
        await checkBal(astETH, lenderAAddress, '1000000000000', 10000);
        await checkBal(stETH, reserveData.aTokenAddress, '2000000000000', 10000);
        await checkSupply(astETH, '2000000000000', 10000);

        await stETH.connect(lenderA.signer).approve(pool.address, await fxtPt(stETH, '1000'));
        await pool
          .connect(lenderA.signer)
          .deposit(stETH.address, await fxtPt(stETH, '1000'), lenderAAddress, '0');

        expect(await astETH.balanceOf(lenderAAddress)).to.eq(await fxtPt(stETH, '1000000001000'));

        await checkBal(stETH, lenderAAddress, '999999999000');
        await checkBal(stETH, lenderBAddress, '500000000000', 10000);
        await checkBal(stETH, lenderCAddress, '500000000000', 10000);
        await checkBal(astETH, lenderAAddress, '1000000001000');
        await checkBal(stETH, reserveData.aTokenAddress, '2000000000000', 10000);
        await checkSupply(astETH, '2000000000000', 10000);
      });
    });

    describe('when borrow>0', function () {
      it('should mint correct number of astETH tokens', async () => {
        const { deployer, dai, pool, stETH, aDai } = testEnv;

        await stETH.connect(lenderA.signer).approve(pool.address, await fxtPt(stETH, '33000'));
        await stETH.connect(lenderB.signer).approve(pool.address, await fxtPt(stETH, '5000'));
        await stETH.connect(lenderC.signer).approve(pool.address, await fxtPt(stETH, '400'));

        await pool
          .connect(lenderA.signer)
          .deposit(stETH.address, await fxtPt(stETH, '30000'), lenderAAddress, '0');
        await pool
          .connect(lenderB.signer)
          .deposit(stETH.address, await fxtPt(stETH, '5000'), lenderBAddress, '0');
        await pool
          .connect(lenderC.signer)
          .deposit(stETH.address, await fxtPt(stETH, '350'), lenderCAddress, '0');

        // borrower borrows 2500 StETH
        await dai.connect(deployer.signer).mint(await fxtPt(dai, '20000'));
        await dai.transfer(borrowerAAddress, await fxtPt(dai, '20000'));
        await dai.connect(borrowerA.signer).approve(pool.address, await fxtPt(dai, '20000'));
        await pool
          .connect(borrowerA.signer)
          .deposit(dai.address, await fxtPt(dai, '20000'), borrowerAAddress, '0');
        await pool
          .connect(borrowerA.signer)
          .borrow(
            stETH.address,
            await fxtPt(stETH, '2500'),
            RateMode.Variable,
            '0',
            borrowerAAddress
          );

        await checkBal(stETH, lenderAAddress, '70000');
        await checkBal(stETH, lenderBAddress, '95000');
        await checkBal(stETH, lenderCAddress, '99650');
        await checkBal(astETH, lenderAAddress, '30000');
        await checkBal(astETH, lenderBAddress, '5000');
        await checkBal(astETH, lenderCAddress, '350');
        await checkBal(stETH, reserveData.aTokenAddress, '32850');
        await checkSupply(astETH, '35350');

        await pool
          .connect(lenderA.signer)
          .deposit(stETH.address, await fxtPt(stETH, '3000'), lenderAAddress, '0');

        expect(await astETH.balanceOf(lenderAAddress)).to.be.bignumber.gte(
          await fxtPt(stETH, '33000')
        );

        await checkBal(stETH, lenderAAddress, '67000');
        await checkBal(stETH, lenderBAddress, '95000');
        await checkBal(stETH, lenderCAddress, '99650');
        await checkBal(astETH, lenderAAddress, '33000');
        await checkBal(astETH, lenderBAddress, '5000');
        await checkBal(astETH, lenderCAddress, '350');
        await checkBal(stETH, reserveData.aTokenAddress, '35850');
        await checkSupply(astETH, '38350');
      });

      it('should update balances on positive rebase', async () => {
        const { deployer, dai, pool, stETH } = testEnv;

        await stETH.connect(lenderA.signer).approve(pool.address, await fxtPt(stETH, '33000'));
        await stETH.connect(lenderB.signer).approve(pool.address, await fxtPt(stETH, '5000'));
        await stETH.connect(lenderC.signer).approve(pool.address, await fxtPt(stETH, '350'));
        await pool
          .connect(lenderA.signer)
          .deposit(stETH.address, await fxtPt(stETH, '33000'), lenderAAddress, '0');
        await pool
          .connect(lenderB.signer)
          .deposit(stETH.address, await fxtPt(stETH, '5000'), lenderBAddress, '0');
        await pool
          .connect(lenderC.signer)
          .deposit(stETH.address, await fxtPt(stETH, '350'), lenderCAddress, '0');

        await dai.connect(deployer.signer).mint(await fxtPt(dai, '20000'));
        await dai.transfer(borrowerAAddress, await fxtPt(dai, '20000'));
        await dai.connect(borrowerA.signer).approve(pool.address, await fxtPt(dai, '20000'));
        await pool
          .connect(borrowerA.signer)
          .deposit(dai.address, await fxtPt(dai, '20000'), borrowerAAddress, '0');
        await pool
          .connect(borrowerA.signer)
          .borrow(
            stETH.address,
            await fxtPt(stETH, '2500'),
            RateMode.Variable,
            '0',
            borrowerAAddress
          );

        await checkBal(stETH, lenderAAddress, '67000');
        await checkBal(stETH, lenderBAddress, '95000');
        await checkBal(stETH, lenderCAddress, '99650');
        await checkBal(astETH, lenderAAddress, '33000');
        await checkBal(astETH, lenderBAddress, '5000');
        await checkBal(astETH, lenderCAddress, '350');
        await checkBal(stETH, reserveData.aTokenAddress, '35850');
        await checkSupply(astETH, '38350');

        await rebase(pool, stETH, +0.1);

        await checkBal(stETH, lenderAAddress, '73700');
        await checkBal(stETH, lenderBAddress, '104500');
        await checkBal(stETH, lenderCAddress, '109615');
        await checkBal(astETH, lenderAAddress, '36084.87');
        await checkBal(astETH, lenderBAddress, '5467.40');
        await checkBal(astETH, lenderCAddress, '382.71');
        await checkBal(stETH, reserveData.aTokenAddress, '39435.00');

        // unborrowed (39435.00) + borrowed (2500)
        await checkSupply(astETH, '41935.00');
      });

      it('should update balances on negative rebase', async () => {
        const { deployer, dai, pool, stETH } = testEnv;

        await stETH.connect(lenderA.signer).approve(pool.address, await fxtPt(stETH, '33000'));
        await stETH.connect(lenderB.signer).approve(pool.address, await fxtPt(stETH, '5000'));
        await stETH.connect(lenderC.signer).approve(pool.address, await fxtPt(stETH, '350'));
        await pool
          .connect(lenderA.signer)
          .deposit(stETH.address, await fxtPt(stETH, '33000'), lenderAAddress, '0');
        await pool
          .connect(lenderB.signer)
          .deposit(stETH.address, await fxtPt(stETH, '5000'), lenderBAddress, '0');
        await pool
          .connect(lenderC.signer)
          .deposit(stETH.address, await fxtPt(stETH, '350'), lenderCAddress, '0');

        await dai.connect(deployer.signer).mint(await fxtPt(dai, '20000'));
        await dai.transfer(borrowerAAddress, await fxtPt(dai, '20000'));
        await dai.connect(borrowerA.signer).approve(pool.address, await fxtPt(dai, '20000'));
        await pool
          .connect(borrowerA.signer)
          .deposit(dai.address, await fxtPt(dai, '20000'), borrowerAAddress, '0');
        await pool
          .connect(borrowerA.signer)
          .borrow(
            stETH.address,
            await fxtPt(stETH, '2500'),
            RateMode.Variable,
            '0',
            borrowerAAddress
          );

        await checkBal(stETH, lenderAAddress, '67000');
        await checkBal(stETH, lenderBAddress, '95000');
        await checkBal(stETH, lenderCAddress, '99650');
        await checkBal(astETH, lenderAAddress, '33000');
        await checkBal(astETH, lenderBAddress, '5000');
        await checkBal(astETH, lenderCAddress, '350');
        await checkBal(stETH, reserveData.aTokenAddress, '35850');
        await checkSupply(astETH, '38350');

        await rebase(pool, stETH, -0.1);

        await checkBal(stETH, lenderAAddress, '60300');
        await checkBal(stETH, lenderBAddress, '85500');
        await checkBal(stETH, lenderCAddress, '89685');
        await checkBal(astETH, lenderAAddress, '29915.12');
        await checkBal(astETH, lenderBAddress, '4532.59');
        await checkBal(astETH, lenderCAddress, '317.28');
        await checkBal(stETH, reserveData.aTokenAddress, '32265');

        // unborrowed (32265.00) + borrowed (2500)
        await checkSupply(astETH, '34765.00');
      });
    });
  });

  describe('user withdraw', function () {
    describe('single deposit partial withdraw', function () {
      it('should burn correct number of astETH tokens', async () => {
        const { pool, stETH } = testEnv;

        await stETH.connect(lenderA.signer).approve(pool.address, await fxtPt(stETH, '1000'));
        await pool
          .connect(lenderA.signer)
          .deposit(stETH.address, await fxtPt(stETH, '1000'), lenderAAddress, '0');

        await checkBal(stETH, lenderAAddress, '99000');
        await checkBal(astETH, lenderAAddress, '1000');
        await checkBal(stETH, reserveData.aTokenAddress, '1000');
        await checkSupply(astETH, '1000');

        await pool
          .connect(lenderA.signer)
          .withdraw(stETH.address, await fxtPt(stETH, '100'), lenderAAddress);

        await checkBal(stETH, lenderAAddress, '99100');
        await checkBal(astETH, lenderAAddress, '900');
        await checkBal(stETH, reserveData.aTokenAddress, '900');
        await checkSupply(astETH, '900');
      });
    });

    describe('single deposit full withdraw', function () {
      it('should burn correct number of astETH tokens', async () => {
        const { pool, stETH } = testEnv;

        await stETH.connect(lenderA.signer).approve(pool.address, await fxtPt(stETH, '1000'));
        await pool
          .connect(lenderA.signer)
          .deposit(stETH.address, await fxtPt(stETH, '1000'), lenderAAddress, '0');

        await checkBal(stETH, lenderAAddress, '99000');
        await checkBal(astETH, lenderAAddress, '1000');
        await checkBal(stETH, reserveData.aTokenAddress, '1000');
        await checkSupply(astETH, '1000');

        await pool.connect(lenderA.signer).withdraw(stETH.address, MAX_UINT_AMOUNT, lenderAAddress);

        await checkBal(stETH, lenderAAddress, '100000');
        await checkBal(astETH, lenderAAddress, '0');
        await checkBal(stETH, reserveData.aTokenAddress, '0');
        await checkSupply(astETH, '0');
      });

      it('should burn correct number of astETH positive rebase', async () => {
        const { pool, stETH } = testEnv;

        await stETH.connect(lenderA.signer).approve(pool.address, await fxtPt(stETH, '1000'));
        await pool
          .connect(lenderA.signer)
          .deposit(stETH.address, await fxtPt(stETH, '1000'), lenderAAddress, '0');

        await checkBal(stETH, lenderAAddress, '99000');
        await checkBal(astETH, lenderAAddress, '1000');
        await checkBal(stETH, reserveData.aTokenAddress, '1000');
        await checkSupply(astETH, '1000');

        await rebase(pool, stETH, 0.1); // + 10%
        await pool.connect(lenderA.signer).withdraw(stETH.address, MAX_UINT_AMOUNT, lenderAAddress);

        await checkBal(stETH, lenderAAddress, '110000');
        await checkBal(astETH, lenderAAddress, '0');
        await checkBal(stETH, reserveData.aTokenAddress, '0');
        await checkSupply(astETH, '0');
      });

      it('should burn correct number of astETH negative rebase', async () => {
        const { pool, stETH } = testEnv;

        await stETH.connect(lenderA.signer).approve(pool.address, await fxtPt(stETH, '1000'));
        await pool
          .connect(lenderA.signer)
          .deposit(stETH.address, await fxtPt(stETH, '1000'), lenderAAddress, '0');

        await checkBal(stETH, lenderAAddress, '99000');
        await checkBal(astETH, lenderAAddress, '1000');
        await checkBal(stETH, reserveData.aTokenAddress, '1000');
        await checkSupply(astETH, '1000');

        await rebase(pool, stETH, -0.1); // - 10%
        await pool.connect(lenderA.signer).withdraw(stETH.address, MAX_UINT_AMOUNT, lenderAAddress);

        await checkBal(stETH, lenderAAddress, '90000');
        await checkBal(astETH, lenderAAddress, '0');
        await checkBal(stETH, reserveData.aTokenAddress, '0');
        await checkSupply(astETH, '0');
      });
    });

    describe('lone user multiple withdraws', function () {
      it('should burn correct number of astETH tokens', async () => {
        const { pool, stETH } = testEnv;

        await stETH.connect(lenderA.signer).approve(pool.address, await fxtPt(stETH, '10000'));
        await pool
          .connect(lenderA.signer)
          .deposit(stETH.address, await fxtPt(stETH, '10000'), lenderAAddress, '0');

        await checkBal(stETH, lenderAAddress, '90000');
        await checkBal(astETH, lenderAAddress, '10000');
        await checkBal(stETH, reserveData.aTokenAddress, '10000');
        await checkSupply(astETH, '10000');

        await pool
          .connect(lenderA.signer)
          .withdraw(stETH.address, await fxtPt(stETH, '1000'), lenderAAddress);

        await checkBal(stETH, lenderAAddress, '91000');
        await checkBal(astETH, lenderAAddress, '9000');
        await checkBal(stETH, reserveData.aTokenAddress, '9000');
        await checkSupply(astETH, '9000');

        await advanceTimeAndBlock(3600 * 24 * 365); // 1 year
        await pool.connect(lenderA.signer).withdraw(stETH.address, MAX_UINT_AMOUNT, lenderAAddress);

        await checkBal(stETH, lenderAAddress, '100000');
        await checkBal(astETH, lenderAAddress, '0');
        await checkBal(stETH, reserveData.aTokenAddress, '0');
        await checkSupply(astETH, '0');
      });
    });

    describe('multiple withdraws', function () {
      it('should burn correct number of astETH tokens', async () => {
        const { pool, stETH } = testEnv;

        await stETH.connect(lenderA.signer).approve(pool.address, await fxtPt(stETH, '33000'));
        await stETH.connect(lenderB.signer).approve(pool.address, await fxtPt(stETH, '5000'));
        await stETH.connect(lenderC.signer).approve(pool.address, await fxtPt(stETH, '350'));

        await pool
          .connect(lenderA.signer)
          .deposit(stETH.address, await fxtPt(stETH, '30000'), lenderAAddress, '0');
        await pool
          .connect(lenderB.signer)
          .deposit(stETH.address, await fxtPt(stETH, '5000'), lenderBAddress, '0');
        await pool
          .connect(lenderC.signer)
          .deposit(stETH.address, await fxtPt(stETH, '350'), lenderCAddress, '0');

        await checkBal(stETH, lenderAAddress, '70000');
        await checkBal(stETH, lenderBAddress, '95000');
        await checkBal(stETH, lenderCAddress, '99650');
        await checkBal(astETH, lenderAAddress, '30000');
        await checkBal(astETH, lenderBAddress, '5000');
        await checkBal(astETH, lenderCAddress, '350');
        await checkBal(stETH, reserveData.aTokenAddress, '35350');
        await checkSupply(astETH, '35350');

        await pool.connect(lenderC.signer).withdraw(stETH.address, MAX_UINT_AMOUNT, lenderCAddress);
        await pool.connect(lenderB.signer).withdraw(stETH.address, MAX_UINT_AMOUNT, lenderBAddress);
        await pool.connect(lenderA.signer).withdraw(stETH.address, MAX_UINT_AMOUNT, lenderAAddress);

        await checkBal(stETH, lenderAAddress, '100000');
        await checkBal(stETH, lenderBAddress, '100000');
        await checkBal(stETH, lenderCAddress, '100000');
        await checkBal(astETH, lenderAAddress, '0');
        await checkBal(astETH, lenderBAddress, '0');
        await checkBal(astETH, lenderCAddress, '0');
        await checkBal(stETH, reserveData.aTokenAddress, '0');
        await checkSupply(astETH, '0');
      });
    });

    describe('v large withdraw', function () {
      it('should burn correct number of astETH tokens', async () => {
        const { deployer, pool, stETH } = testEnv;

        await stETH.connect(deployer.signer).transfer(lenderAAddress, await fxtPt(stETH, '100000'));
        await rebase(pool, stETH, 9999999);
        await checkSupply(stETH, '500000000000000'); // 500T

        await stETH
          .connect(lenderA.signer)
          .approve(pool.address, await fxtPt(stETH, '1000000000000')); // 1T
        await stETH
          .connect(lenderB.signer)
          .approve(pool.address, await fxtPt(stETH, '500000000000')); // 0.5T
        await stETH
          .connect(lenderC.signer)
          .approve(pool.address, await fxtPt(stETH, '500000000000')); // 0.5T
        await pool
          .connect(lenderA.signer)
          .deposit(stETH.address, await fxtPt(stETH, '1000000000000'), lenderAAddress, '0');
        await pool
          .connect(lenderB.signer)
          .deposit(stETH.address, await fxtPt(stETH, '500000000000'), lenderBAddress, '0');
        await pool
          .connect(lenderC.signer)
          .deposit(stETH.address, await fxtPt(stETH, '500000000000'), lenderCAddress, '0');

        await checkBal(stETH, lenderAAddress, '1000000000000', 10000);
        await checkBal(stETH, lenderBAddress, '500000000000', 10000);
        await checkBal(stETH, lenderCAddress, '500000000000', 10000);
        await checkBal(astETH, lenderAAddress, '1000000000000', 10000);
        await checkBal(stETH, reserveData.aTokenAddress, '2000000000000', 10000);
        await checkSupply(astETH, '2000000000000', 10000);

        await pool.connect(lenderA.signer).withdraw(stETH.address, MAX_UINT_AMOUNT, lenderAAddress);

        await checkBal(stETH, lenderAAddress, '2000000000000', 10000);
        await checkBal(stETH, lenderBAddress, '500000000000', 10000);
        await checkBal(stETH, lenderCAddress, '500000000000', 10000);
        await checkBal(astETH, lenderAAddress, '0');
        await checkBal(stETH, reserveData.aTokenAddress, '1000000000000', 10000);
        await checkSupply(astETH, '1000000000000', 10000);
      });
    });

    describe('when borrow>0', function () {
      it('should burn correct number of astETH tokens', async () => {
        const { deployer, dai, pool, stETH } = testEnv;

        await stETH.connect(lenderA.signer).approve(pool.address, await fxtPt(stETH, '33000'));
        await stETH.connect(lenderB.signer).approve(pool.address, await fxtPt(stETH, '5000'));
        await stETH.connect(lenderC.signer).approve(pool.address, await fxtPt(stETH, '350'));
        await pool
          .connect(lenderA.signer)
          .deposit(stETH.address, await fxtPt(stETH, '33000'), lenderAAddress, '0');
        await pool
          .connect(lenderB.signer)
          .deposit(stETH.address, await fxtPt(stETH, '5000'), lenderBAddress, '0');
        await pool
          .connect(lenderC.signer)
          .deposit(stETH.address, await fxtPt(stETH, '350'), lenderCAddress, '0');

        // borrower borrows 2500 StETH
        await dai.connect(deployer.signer).mint(await fxtPt(dai, '20000'));
        await dai.transfer(borrowerAAddress, await fxtPt(dai, '20000'));
        await dai.connect(borrowerA.signer).approve(pool.address, await fxtPt(dai, '20000'));
        await pool
          .connect(borrowerA.signer)
          .deposit(dai.address, await fxtPt(dai, '20000'), borrowerAAddress, '0');
        await pool
          .connect(borrowerA.signer)
          .borrow(
            stETH.address,
            await fxtPt(stETH, '2500'),
            RateMode.Variable,
            '0',
            borrowerAAddress
          );

        await checkBal(stETH, lenderAAddress, '67000');
        await checkBal(stETH, lenderBAddress, '95000');
        await checkBal(stETH, lenderCAddress, '99650');
        await checkBal(astETH, lenderAAddress, '33000');
        await checkBal(astETH, lenderBAddress, '5000');
        await checkBal(astETH, lenderCAddress, '350');
        await checkBal(stETH, reserveData.aTokenAddress, '35850');
        await checkSupply(astETH, '38350');

        await pool.connect(lenderC.signer).withdraw(stETH.address, MAX_UINT_AMOUNT, lenderCAddress);

        await checkBal(stETH, lenderAAddress, '67000');
        await checkBal(stETH, lenderBAddress, '95000');
        await checkBal(stETH, lenderCAddress, '100000');
        await checkBal(astETH, lenderAAddress, '33000');
        await checkBal(astETH, lenderBAddress, '5000');
        await checkBal(astETH, lenderCAddress, '0');
        await checkBal(stETH, reserveData.aTokenAddress, '35500');
        await checkSupply(astETH, '38000');
      });

      it('should update balances on positive rebase', async () => {
        const { deployer, dai, pool, stETH } = testEnv;

        await stETH.connect(lenderA.signer).approve(pool.address, await fxtPt(stETH, '33000'));
        await stETH.connect(lenderB.signer).approve(pool.address, await fxtPt(stETH, '5000'));
        await stETH.connect(lenderC.signer).approve(pool.address, await fxtPt(stETH, '350'));
        await pool
          .connect(lenderA.signer)
          .deposit(stETH.address, await fxtPt(stETH, '33000'), lenderAAddress, '0');
        await pool
          .connect(lenderB.signer)
          .deposit(stETH.address, await fxtPt(stETH, '5000'), lenderBAddress, '0');
        await pool
          .connect(lenderC.signer)
          .deposit(stETH.address, await fxtPt(stETH, '350'), lenderCAddress, '0');

        // borrower borrows 2500 StETH
        await dai.connect(deployer.signer).mint(await fxtPt(dai, '20000'));
        await dai.transfer(borrowerAAddress, await fxtPt(dai, '20000'));
        await dai.connect(borrowerA.signer).approve(pool.address, await fxtPt(dai, '20000'));
        await pool
          .connect(borrowerA.signer)
          .deposit(dai.address, await fxtPt(dai, '20000'), borrowerAAddress, '0');
        await pool
          .connect(borrowerA.signer)
          .borrow(
            stETH.address,
            await fxtPt(stETH, '2500'),
            RateMode.Variable,
            '0',
            borrowerAAddress
          );

        await checkBal(stETH, lenderAAddress, '67000');
        await checkBal(stETH, lenderBAddress, '95000');
        await checkBal(stETH, lenderCAddress, '99650');
        await checkBal(astETH, lenderAAddress, '33000');
        await checkBal(astETH, lenderBAddress, '5000');
        await checkBal(astETH, lenderCAddress, '350');
        await checkBal(stETH, reserveData.aTokenAddress, '35850');
        await checkSupply(astETH, '38350');

        await rebase(pool, stETH, +0.1);
        await pool.connect(lenderC.signer).withdraw(stETH.address, MAX_UINT_AMOUNT, lenderCAddress);

        await checkBal(stETH, lenderAAddress, '73700');
        await checkBal(stETH, lenderBAddress, '104500');
        await checkBal(stETH, lenderCAddress, '109997.71');
        await checkBal(astETH, lenderAAddress, '36084.87');
        await checkBal(astETH, lenderBAddress, '5467.40');
        await checkBal(astETH, lenderCAddress, '0');
        await checkBal(stETH, reserveData.aTokenAddress, '39052.28');
        await checkSupply(astETH, '41552.28');
      });

      it('should update balances on negative rebase', async () => {
        const { deployer, dai, pool, stETH } = testEnv;

        await stETH.connect(lenderA.signer).approve(pool.address, await fxtPt(stETH, '33000'));
        await stETH.connect(lenderB.signer).approve(pool.address, await fxtPt(stETH, '5000'));
        await stETH.connect(lenderC.signer).approve(pool.address, await fxtPt(stETH, '350'));
        await pool
          .connect(lenderA.signer)
          .deposit(stETH.address, await fxtPt(stETH, '33000'), lenderAAddress, '0');
        await pool
          .connect(lenderB.signer)
          .deposit(stETH.address, await fxtPt(stETH, '5000'), lenderBAddress, '0');
        await pool
          .connect(lenderC.signer)
          .deposit(stETH.address, await fxtPt(stETH, '350'), lenderCAddress, '0');

        // borrower borrows 2500 StETH
        await dai.connect(deployer.signer).mint(await fxtPt(dai, '20000'));
        await dai.transfer(borrowerAAddress, await fxtPt(dai, '20000'));
        await dai.connect(borrowerA.signer).approve(pool.address, await fxtPt(dai, '20000'));
        await pool
          .connect(borrowerA.signer)
          .deposit(dai.address, await fxtPt(dai, '20000'), borrowerAAddress, '0');
        await pool
          .connect(borrowerA.signer)
          .borrow(
            stETH.address,
            await fxtPt(stETH, '2500'),
            RateMode.Variable,
            '0',
            borrowerAAddress
          );

        await checkBal(stETH, lenderAAddress, '67000');
        await checkBal(stETH, lenderBAddress, '95000');
        await checkBal(stETH, lenderCAddress, '99650');
        await checkBal(astETH, lenderAAddress, '33000');
        await checkBal(astETH, lenderBAddress, '5000');
        await checkBal(astETH, lenderCAddress, '350');
        await checkBal(stETH, reserveData.aTokenAddress, '35850');
        await checkSupply(astETH, '38350');

        await rebase(pool, stETH, -0.1);
        await pool.connect(lenderC.signer).withdraw(stETH.address, MAX_UINT_AMOUNT, lenderCAddress);

        await checkBal(stETH, lenderAAddress, '60300');
        await checkBal(stETH, lenderBAddress, '85500');
        await checkBal(stETH, lenderCAddress, '90002.28');
        await checkBal(astETH, lenderAAddress, '29915.12');
        await checkBal(astETH, lenderBAddress, '4532.59');
        await checkBal(astETH, lenderCAddress, '0');
        await checkBal(stETH, reserveData.aTokenAddress, '31947.72');
        await checkSupply(astETH, '34447.72');
      });
    });
  });

  describe('user borrow repay with interest', function () {
    it('should update accounting', async () => {
      const { pool, dai, stETH, aDai, helpersContract } = testEnv;

      // lender deposits StETH
      await stETH.connect(lenderA.signer).approve(pool.address, await fxtPt(stETH, '10000'));
      await pool
        .connect(lenderA.signer)
        .deposit(stETH.address, await fxtPt(stETH, '10000'), lenderAAddress, '0');

      // borrower deposits DAI
      await dai.mint(await fxtPt(dai, '20000'));
      await dai.transfer(borrowerAAddress, await fxtPt(dai, '20000'));
      await dai.connect(borrowerA.signer).approve(pool.address, await fxtPt(dai, '20000'));
      await pool
        .connect(borrowerA.signer)
        .deposit(dai.address, await fxtPt(dai, '20000'), borrowerAAddress, '0');

      await checkBal(stETH, lenderAAddress, '90000');
      await checkBal(astETH, lenderAAddress, '10000');
      await checkSupply(astETH, '10000');
      await checkBal(stETH, reserveData.aTokenAddress, '10000');
      await checkBal(stETH, borrowerAAddress, '0');
      await checkBal(debtToken, borrowerAAddress, '0');

      // borrower borrows StETH
      await pool
        .connect(borrowerA.signer)
        .borrow(
          stETH.address,
          await fxtPt(stETH, '2500'),
          RateMode.Variable,
          '0',
          borrowerAAddress
        );

      await checkBal(stETH, lenderAAddress, '90000');
      await checkBal(astETH, lenderAAddress, '10000');
      await checkSupply(astETH, '10000');
      await checkBal(stETH, reserveData.aTokenAddress, '7500');
      await checkBal(stETH, borrowerAAddress, '2500');
      await checkBal(debtToken, borrowerAAddress, '2500');

      await advanceTimeAndBlock(10 * 3600 * 24 * 365); // 10 years

      await checkBal(stETH, lenderAAddress, '90000');
      await checkScaledBal(astETH, lenderAAddress, '10000'); // P = 7500 + 2500
      await checkBal(astETH, lenderAAddress, '10208.33'); // T = P + 208.33 (I)
      await checkSupply(astETH, '10208.33');
      await checkBal(stETH, reserveData.aTokenAddress, '7500'); // unborrowed pool balance
      await checkBal(stETH, borrowerAAddress, '2500'); // borrower StETH balance
      await checkBal(debtToken, borrowerAAddress, '2717.01'); // 2500 (principal) + 217.01 (I)
      await checkBal(astETH, treasuryAddress, '0');

      // borrower gets some StETH to close out debt
      await stETH.connect(lenderC.signer).transfer(borrowerAAddress, await fxtPt(stETH, '300'));
      await checkBal(stETH, borrowerAAddress, '2800', 1);

      // borrower repays 2500 + 208.33 + 29.51 StETH
      await stETH.connect(borrowerA.signer).approve(pool.address, MAX_UINT_AMOUNT);
      await pool
        .connect(borrowerA.signer)
        .repay(stETH.address, MAX_UINT_AMOUNT, RateMode.Variable, borrowerAAddress);

      await checkBal(stETH, lenderAAddress, '90000');
      await checkBal(astETH, lenderAAddress, '10208.33');
      await checkSupply(astETH, '10208.33');
      await checkBal(stETH, reserveData.aTokenAddress, '10217.01');
      await checkBal(stETH, borrowerAAddress, '82.99');
      await checkBal(debtToken, borrowerAAddress, '0');
      await checkBal(astETH, treasuryAddress, '0');

      await pool.connect(lenderA.signer).withdraw(stETH.address, MAX_UINT_AMOUNT, lenderAAddress);

      await checkBal(stETH, lenderAAddress, '100208.33');
      await checkBal(astETH, lenderAAddress, '0');
      await checkSupply(astETH, '0');
      await checkBal(stETH, reserveData.aTokenAddress, '8.68');
      await checkBal(astETH, treasuryAddress, '0');
    });
  });

  describe('user borrow repay with positive rebase', function () {
    it('should update accounting', async () => {
      const { pool, dai, stETH, aDai, helpersContract } = testEnv;

      // lender deposits StETH
      await stETH.connect(lenderA.signer).approve(pool.address, await fxtPt(stETH, '10000'));
      await pool
        .connect(lenderA.signer)
        .deposit(stETH.address, await fxtPt(stETH, '10000'), lenderAAddress, '0');

      // borrower deposits DAI
      await dai.mint(await fxtPt(dai, '20000'));
      await dai.transfer(borrowerAAddress, await fxtPt(dai, '20000'));
      await dai.connect(borrowerA.signer).approve(pool.address, await fxtPt(dai, '20000'));
      await pool
        .connect(borrowerA.signer)
        .deposit(dai.address, await fxtPt(dai, '20000'), borrowerAAddress, '0');

      // borrower borrows StETH
      await pool
        .connect(borrowerA.signer)
        .borrow(
          stETH.address,
          await fxtPt(stETH, '2500'),
          RateMode.Variable,
          '0',
          borrowerAAddress
        );

      await advanceTimeAndBlock(10 * 3600 * 24 * 365); // 10 years

      await rebase(pool, stETH, +0.25); // 25% rebase

      await checkBal(stETH, lenderAAddress, '112500');
      await checkScaledBal(astETH, lenderAAddress, '11875.00'); // P = (7500*1.25) + 2500
      await checkBal(astETH, lenderAAddress, '12122.39'); // T = P + 247.39 (I)
      await checkSupply(astETH, '12122.39');
      await checkBal(stETH, reserveData.aTokenAddress, '9375'); // unborrowed principal balance (7500*1.25)
      await checkBal(stETH, borrowerAAddress, '3125.00'); // Borrowed StETH balance
      await checkBal(debtToken, borrowerAAddress, '2717.01'); // 2500 (principal) + 217.01 (I)
      await checkBal(astETH, treasuryAddress, '0'); // Treasury

      // borrower repays 2500 + 244.86 StETH
      await stETH.connect(borrowerA.signer).approve(pool.address, MAX_UINT_AMOUNT);
      await pool
        .connect(borrowerA.signer)
        .repay(stETH.address, MAX_UINT_AMOUNT, RateMode.Variable, borrowerAAddress);

      await checkBal(stETH, lenderAAddress, '112500');
      await checkScaledBal(astETH, lenderAAddress, '11875.00');
      await checkBal(astETH, lenderAAddress, '12122.39');
      await checkSupply(astETH, '12122.39');
      await checkBal(stETH, reserveData.aTokenAddress, '12092.01');
      await checkBal(stETH, borrowerAAddress, '407.98');
      await checkBal(debtToken, borrowerAAddress, '0');
      await checkBal(astETH, treasuryAddress, '0');

      await pool.connect(lenderA.signer).withdraw(
        stETH.address,
        await fxtPt(stETH, '12090'),
        // MAX_UINT_AMOUNT,
        lenderAAddress
      );

      await checkBal(stETH, lenderAAddress, '124590.00');
      await checkScaledBal(astETH, lenderAAddress, '31.73');
      await checkBal(astETH, lenderAAddress, '32.39');
      await checkSupply(astETH, '32.39');
      await checkBal(stETH, reserveData.aTokenAddress, '2.01');
      await checkBal(stETH, borrowerAAddress, '407.98');
      await checkBal(debtToken, borrowerAAddress, '0');
      await checkBal(astETH, treasuryAddress, '0');
    });
  });

  describe('user borrow repay with negative rebase', function () {
    it('should update accounting', async () => {
      const { pool, dai, stETH, aDai, helpersContract } = testEnv;

      // lender deposits StETH
      await stETH.connect(lenderA.signer).approve(pool.address, await fxtPt(stETH, '10000'));
      await pool
        .connect(lenderA.signer)
        .deposit(stETH.address, await fxtPt(stETH, '10000'), lenderAAddress, '0');

      // borrower deposits DAI
      await dai.mint(await fxtPt(dai, '20000'));
      await dai.transfer(borrowerAAddress, await fxtPt(dai, '20000'));
      await dai.connect(borrowerA.signer).approve(pool.address, await fxtPt(dai, '20000'));
      await pool
        .connect(borrowerA.signer)
        .deposit(dai.address, await fxtPt(dai, '20000'), borrowerAAddress, '0');

      // borrower borrows StETH
      await pool
        .connect(borrowerA.signer)
        .borrow(
          stETH.address,
          await fxtPt(stETH, '2500'),
          RateMode.Variable,
          '0',
          borrowerAAddress
        );

      await advanceTimeAndBlock(10 * 3600 * 24 * 365); // 10 years
      await rebase(pool, stETH, -0.25); // -25% rebase

      await checkBal(stETH, lenderAAddress, '67500.00');
      await checkScaledBal(astETH, lenderAAddress, '8125'); // P = (7500*0.75) + 2500
      await checkBal(astETH, lenderAAddress, '8294.27'); // T = P + 169.27 (I)
      await checkSupply(astETH, '8294.27');
      await checkBal(stETH, reserveData.aTokenAddress, '5625.00'); // unborrowed principal balance (7500*0.75)
      await checkBal(stETH, borrowerAAddress, '1875.00'); // Borrowed StETH balance
      await checkBal(debtToken, borrowerAAddress, '2717.01'); // 2500 (principal) + 217.01 (I)
      await checkBal(astETH, treasuryAddress, '0'); // Treasury

      // friend sends borrower some stETH to pay back interest
      await stETH.connect(lenderC.signer).transfer(borrowerAAddress, await fxtPt(stETH, '1000'));

      // borrower repays 2500 + 365.25 StETH
      await stETH.connect(borrowerA.signer).approve(pool.address, MAX_UINT_AMOUNT);
      await pool
        .connect(borrowerA.signer)
        .repay(stETH.address, MAX_UINT_AMOUNT, RateMode.Variable, borrowerAAddress);

      await checkBal(stETH, lenderAAddress, '67500.00');
      await checkScaledBal(astETH, lenderAAddress, '8125');
      await checkBal(astETH, lenderAAddress, '8294.27');
      await checkSupply(astETH, '8294.27');
      await checkBal(stETH, reserveData.aTokenAddress, '8342.01');
      await checkBal(stETH, borrowerAAddress, '157.98');
      await checkBal(debtToken, borrowerAAddress, '0');
      await checkBal(astETH, treasuryAddress, '0');

      await pool.connect(lenderA.signer).withdraw(stETH.address, MAX_UINT_AMOUNT, lenderAAddress);

      await checkBal(stETH, lenderAAddress, '75794.27');
      await checkScaledBal(astETH, lenderAAddress, '0');
      await checkBal(astETH, lenderAAddress, '0');
      await checkSupply(astETH, '0');
      await checkBal(stETH, reserveData.aTokenAddress, '47.74');
      await checkBal(stETH, borrowerAAddress, '157.98');
      await checkBal(debtToken, borrowerAAddress, '0');
      await checkBal(astETH, treasuryAddress, '0');
    });
  });

  describe('multi user borrow repay', function () {
    it('should update accounting', async () => {
      const { pool, dai, stETH, aDai, helpersContract } = testEnv;

      // lender deposits StETH
      await stETH.connect(lenderA.signer).approve(pool.address, await fxtPt(stETH, '10000'));
      await pool
        .connect(lenderA.signer)
        .deposit(stETH.address, await fxtPt(stETH, '10000'), lenderAAddress, '0');

      await stETH.connect(lenderB.signer).approve(pool.address, await fxtPt(stETH, '5000'));
      await pool
        .connect(lenderB.signer)
        .deposit(stETH.address, await fxtPt(stETH, '5000'), lenderBAddress, '0');

      await stETH.connect(lenderC.signer).approve(pool.address, await fxtPt(stETH, '2500'));
      await pool
        .connect(lenderC.signer)
        .deposit(stETH.address, await fxtPt(stETH, '2500'), lenderCAddress, '0');

      // borrowers deposits DAI and borrow StETH
      await dai.mint(await fxtPt(dai, '1000000'));
      await dai.transfer(borrowerAAddress, await fxtPt(dai, '30000'));
      await dai.transfer(borrowerBAddress, await fxtPt(dai, '50000'));
      await dai.connect(borrowerA.signer).approve(pool.address, await fxtPt(dai, '30000'));
      await dai.connect(borrowerB.signer).approve(pool.address, await fxtPt(dai, '50000'));

      await pool
        .connect(borrowerA.signer)
        .deposit(dai.address, await fxtPt(dai, '20000'), borrowerAAddress, '0');
      await pool
        .connect(borrowerB.signer)
        .deposit(dai.address, await fxtPt(dai, '40000'), borrowerBAddress, '0');

      await pool
        .connect(borrowerA.signer)
        .borrow(
          stETH.address,
          await fxtPt(stETH, '2500'),
          RateMode.Variable,
          '0',
          borrowerAAddress
        );

      await pool
        .connect(borrowerB.signer)
        .borrow(
          stETH.address,
          await fxtPt(stETH, '5000'),
          RateMode.Variable,
          '0',
          borrowerBAddress
        );

      // time passes and supply changes
      await advanceTimeAndBlock(10 * 3600 * 24 * 365); // 10 years
      await rebase(pool, stETH, 0.5); // +50% rebase

      // borrower A repays
      await stETH.connect(borrowerA.signer).approve(pool.address, MAX_UINT_AMOUNT);
      await pool
        .connect(borrowerA.signer)
        .repay(stETH.address, MAX_UINT_AMOUNT, RateMode.Variable, borrowerAAddress);

      // time passes and supply changes
      await advanceTimeAndBlock(10 * 3600 * 24 * 365); // 10 years
      await rebase(pool, stETH, -0.05); // -5% rebase
      // lenders pull out
      await pool.connect(lenderC.signer).withdraw(stETH.address, MAX_UINT_AMOUNT, lenderAAddress);
      // borrower B repays
      await stETH.connect(borrowerB.signer).approve(pool.address, MAX_UINT_AMOUNT);
      await pool
        .connect(borrowerB.signer)
        .repay(stETH.address, MAX_UINT_AMOUNT, RateMode.Variable, borrowerBAddress);

      // time passes and supply changes
      await advanceTimeAndBlock(10 * 3600 * 24 * 365); // 10 years
      await rebase(pool, stETH, -0.1); // -10% rebase

      // lenders pull out
      await pool.connect(lenderA.signer).withdraw(stETH.address, MAX_UINT_AMOUNT, lenderAAddress);
      await pool
        .connect(lenderB.signer)
        .withdraw(stETH.address, await fxtPt(stETH, '5872'), lenderAAddress);

      await checkBal(astETH, lenderAAddress, '0');
      await checkBal(astETH, lenderBAddress, '146.08');
      await checkBal(astETH, lenderCAddress, '0');
      await checkBal(debtToken, borrowerAAddress, '0');
      await checkBal(debtToken, borrowerBAddress, '0');
      await checkSupply(astETH, '146.08');
      await checkBal(stETH, reserveData.aTokenAddress, '0.04');
      await checkBal(astETH, treasuryAddress, '0');
    });
  });
});
