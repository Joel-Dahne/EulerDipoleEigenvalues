module

public import EulerDipoleEigenvalues.Certificates.Inequalities.MixedOddBLog
public import EulerDipoleEigenvalues.Certificates.Inequalities.MixedOddBStripData

/-!
# Endpoint polynomial identities for the odd-in-b strips

Normalize each integer power table against the cleared logarithm endpoint.
The independent subdivision arithmetic does not enter these identities.
-/

@[expose] public section

namespace EulerDipoleEigenvalues

private theorem logTwoLower_real : (certificateLogTwoLower : ℝ) =
    (52112452242329513449286024495168 : ℝ) / 75182376418571730210283091385675 := by
  have h : certificateLogTwoLower =
      (52112452242329513449286024495168 : ℚ) / 75182376418571730210283091385675 := by
    decide +kernel
  rw [h]
  push_cast
  rfl

private theorem logTwoUpper_real : (certificateLogTwoUpper : ℝ) =
    (8546442167742040205701459862544577 : ℝ) / 12329909732645763754486426987250700 := by
  have h : certificateLogTwoUpper =
      (8546442167742040205701459862544577 : ℚ) / 12329909732645763754486426987250700 := by
    decide +kernel
  rw [h]
  push_cast
  rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
-- Normalize the full integer coefficient table against the factored endpoint.
theorem oddBLower0_power (z k : ℝ) :
    bernsteinIntPowerEval oddBLower0Power z k =
      (oddBLower0Scale : ℝ) * mixedOddBStripLower 0 z k := by
  simp only [mixedOddBStripLower, mixed_odd_b_cleared_affine, mixedOddBStripH,
    mixed_odd_b_a_table, mixed_odd_b_b_table, certificateLogTaylor, logTwoUpper_real]
  simp [bernsteinIntPowerEval, certificatePolynomial, oddBLower0Power, oddBLower0Scale,
    mixedOddBAPower, mixedOddBBPower, mixedOddBAInt, mixedOddBBInt, Fin.sum_univ_succ,
    Finset.sum_range_succ, Vector.get, Vector.getElem_mk]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
-- Normalize the full integer coefficient table against the factored endpoint.
theorem oddBUpper0_power (z k : ℝ) :
    bernsteinIntPowerEval oddBUpper0Power z k =
      (oddBUpper0Scale : ℝ) * mixedOddBStripUpper 0 z k := by
  simp only [mixedOddBStripUpper, mixed_odd_b_cleared_affine, mixedOddBStripH,
    mixed_odd_b_a_table, mixed_odd_b_b_table, certificateLogTaylor, logTwoLower_real]
  simp [bernsteinIntPowerEval, certificatePolynomial, oddBUpper0Power, oddBUpper0Scale,
    mixedOddBAPower, mixedOddBBPower, mixedOddBAInt, mixedOddBBInt, Fin.sum_univ_succ,
    Finset.sum_range_succ, Vector.get, Vector.getElem_mk]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
-- Normalize the full integer coefficient table against the factored endpoint.
theorem oddBLower1_power (z k : ℝ) :
    bernsteinIntPowerEval oddBLower1Power z k =
      (oddBLower1Scale : ℝ) * mixedOddBStripLower 1 z k := by
  simp only [mixedOddBStripLower, mixed_odd_b_cleared_affine, mixedOddBStripH,
    mixed_odd_b_a_table, mixed_odd_b_b_table, certificateLogTaylor, logTwoUpper_real]
  simp [bernsteinIntPowerEval, certificatePolynomial, oddBLower1Power, oddBLower1Scale,
    mixedOddBAPower, mixedOddBBPower, mixedOddBAInt, mixedOddBBInt, Fin.sum_univ_succ,
    Finset.sum_range_succ, Vector.get, Vector.getElem_mk]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
-- Normalize the full integer coefficient table against the factored endpoint.
theorem oddBUpper1_power (z k : ℝ) :
    bernsteinIntPowerEval oddBUpper1Power z k =
      (oddBUpper1Scale : ℝ) * mixedOddBStripUpper 1 z k := by
  simp only [mixedOddBStripUpper, mixed_odd_b_cleared_affine, mixedOddBStripH,
    mixed_odd_b_a_table, mixed_odd_b_b_table, certificateLogTaylor, logTwoLower_real]
  simp [bernsteinIntPowerEval, certificatePolynomial, oddBUpper1Power, oddBUpper1Scale,
    mixedOddBAPower, mixedOddBBPower, mixedOddBAInt, mixedOddBBInt, Fin.sum_univ_succ,
    Finset.sum_range_succ, Vector.get, Vector.getElem_mk]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
-- Normalize the full integer coefficient table against the factored endpoint.
theorem oddBLower2_power (z k : ℝ) :
    bernsteinIntPowerEval oddBLower2Power z k =
      (oddBLower2Scale : ℝ) * mixedOddBStripLower 2 z k := by
  simp only [mixedOddBStripLower, mixed_odd_b_cleared_affine, mixedOddBStripH,
    mixed_odd_b_a_table, mixed_odd_b_b_table, certificateLogTaylor, logTwoUpper_real]
  simp [bernsteinIntPowerEval, certificatePolynomial, oddBLower2Power, oddBLower2Scale,
    mixedOddBAPower, mixedOddBBPower, mixedOddBAInt, mixedOddBBInt, Fin.sum_univ_succ,
    Finset.sum_range_succ, Vector.get, Vector.getElem_mk]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
-- Normalize the full integer coefficient table against the factored endpoint.
theorem oddBUpper2_power (z k : ℝ) :
    bernsteinIntPowerEval oddBUpper2Power z k =
      (oddBUpper2Scale : ℝ) * mixedOddBStripUpper 2 z k := by
  simp only [mixedOddBStripUpper, mixed_odd_b_cleared_affine, mixedOddBStripH,
    mixed_odd_b_a_table, mixed_odd_b_b_table, certificateLogTaylor, logTwoLower_real]
  simp [bernsteinIntPowerEval, certificatePolynomial, oddBUpper2Power, oddBUpper2Scale,
    mixedOddBAPower, mixedOddBBPower, mixedOddBAInt, mixedOddBBInt, Fin.sum_univ_succ,
    Finset.sum_range_succ, Vector.get, Vector.getElem_mk]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
-- Normalize the full integer coefficient table against the factored endpoint.
theorem oddBLower3_power (z k : ℝ) :
    bernsteinIntPowerEval oddBLower3Power z k =
      (oddBLower3Scale : ℝ) * mixedOddBStripLower 3 z k := by
  simp only [mixedOddBStripLower, mixed_odd_b_cleared_affine, mixedOddBStripH,
    mixed_odd_b_a_table, mixed_odd_b_b_table, certificateLogTaylor, logTwoUpper_real]
  simp [bernsteinIntPowerEval, certificatePolynomial, oddBLower3Power, oddBLower3Scale,
    mixedOddBAPower, mixedOddBBPower, mixedOddBAInt, mixedOddBBInt, Fin.sum_univ_succ,
    Finset.sum_range_succ, Vector.get, Vector.getElem_mk]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
-- Normalize the full integer coefficient table against the factored endpoint.
theorem oddBUpper3_power (z k : ℝ) :
    bernsteinIntPowerEval oddBUpper3Power z k =
      (oddBUpper3Scale : ℝ) * mixedOddBStripUpper 3 z k := by
  simp only [mixedOddBStripUpper, mixed_odd_b_cleared_affine, mixedOddBStripH,
    mixed_odd_b_a_table, mixed_odd_b_b_table, certificateLogTaylor, logTwoLower_real]
  simp [bernsteinIntPowerEval, certificatePolynomial, oddBUpper3Power, oddBUpper3Scale,
    mixedOddBAPower, mixedOddBBPower, mixedOddBAInt, mixedOddBBInt, Fin.sum_univ_succ,
    Finset.sum_range_succ, Vector.get, Vector.getElem_mk]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
-- Normalize the full integer coefficient table against the factored endpoint.
theorem oddBLower4_power (z k : ℝ) :
    bernsteinIntPowerEval oddBLower4Power z k =
      (oddBLower4Scale : ℝ) * mixedOddBStripLower 4 z k := by
  simp only [mixedOddBStripLower, mixed_odd_b_cleared_affine, mixedOddBStripH,
    mixed_odd_b_a_table, mixed_odd_b_b_table, certificateLogTaylor, logTwoUpper_real]
  simp [bernsteinIntPowerEval, certificatePolynomial, oddBLower4Power, oddBLower4Scale,
    mixedOddBAPower, mixedOddBBPower, mixedOddBAInt, mixedOddBBInt, Fin.sum_univ_succ,
    Finset.sum_range_succ, Vector.get, Vector.getElem_mk]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
-- Normalize the full integer coefficient table against the factored endpoint.
theorem oddBUpper4_power (z k : ℝ) :
    bernsteinIntPowerEval oddBUpper4Power z k =
      (oddBUpper4Scale : ℝ) * mixedOddBStripUpper 4 z k := by
  simp only [mixedOddBStripUpper, mixed_odd_b_cleared_affine, mixedOddBStripH,
    mixed_odd_b_a_table, mixed_odd_b_b_table, certificateLogTaylor, logTwoLower_real]
  simp [bernsteinIntPowerEval, certificatePolynomial, oddBUpper4Power, oddBUpper4Scale,
    mixedOddBAPower, mixedOddBBPower, mixedOddBAInt, mixedOddBBInt, Fin.sum_univ_succ,
    Finset.sum_range_succ, Vector.get, Vector.getElem_mk]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
-- Normalize the full integer coefficient table against the factored endpoint.
theorem oddBLower5_power (z k : ℝ) :
    bernsteinIntPowerEval oddBLower5Power z k =
      (oddBLower5Scale : ℝ) * mixedOddBStripLower 5 z k := by
  simp only [mixedOddBStripLower, mixed_odd_b_cleared_affine, mixedOddBStripH,
    mixed_odd_b_a_table, mixed_odd_b_b_table, certificateLogTaylor, logTwoUpper_real]
  simp [bernsteinIntPowerEval, certificatePolynomial, oddBLower5Power, oddBLower5Scale,
    mixedOddBAPower, mixedOddBBPower, mixedOddBAInt, mixedOddBBInt, Fin.sum_univ_succ,
    Finset.sum_range_succ, Vector.get, Vector.getElem_mk]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
-- Normalize the full integer coefficient table against the factored endpoint.
theorem oddBUpper5_power (z k : ℝ) :
    bernsteinIntPowerEval oddBUpper5Power z k =
      (oddBUpper5Scale : ℝ) * mixedOddBStripUpper 5 z k := by
  simp only [mixedOddBStripUpper, mixed_odd_b_cleared_affine, mixedOddBStripH,
    mixed_odd_b_a_table, mixed_odd_b_b_table, certificateLogTaylor, logTwoLower_real]
  simp [bernsteinIntPowerEval, certificatePolynomial, oddBUpper5Power, oddBUpper5Scale,
    mixedOddBAPower, mixedOddBBPower, mixedOddBAInt, mixedOddBBInt, Fin.sum_univ_succ,
    Finset.sum_range_succ, Vector.get, Vector.getElem_mk]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
-- Normalize the full integer coefficient table against the factored endpoint.
theorem oddBLower6_power (z k : ℝ) :
    bernsteinIntPowerEval oddBLower6Power z k =
      (oddBLower6Scale : ℝ) * mixedOddBStripLower 6 z k := by
  simp only [mixedOddBStripLower, mixed_odd_b_cleared_affine, mixedOddBStripH,
    mixed_odd_b_a_table, mixed_odd_b_b_table, certificateLogTaylor, logTwoUpper_real]
  simp [bernsteinIntPowerEval, certificatePolynomial, oddBLower6Power, oddBLower6Scale,
    mixedOddBAPower, mixedOddBBPower, mixedOddBAInt, mixedOddBBInt, Fin.sum_univ_succ,
    Finset.sum_range_succ, Vector.get, Vector.getElem_mk]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
-- Normalize the full integer coefficient table against the factored endpoint.
theorem oddBUpper6_power (z k : ℝ) :
    bernsteinIntPowerEval oddBUpper6Power z k =
      (oddBUpper6Scale : ℝ) * mixedOddBStripUpper 6 z k := by
  simp only [mixedOddBStripUpper, mixed_odd_b_cleared_affine, mixedOddBStripH,
    mixed_odd_b_a_table, mixed_odd_b_b_table, certificateLogTaylor, logTwoLower_real]
  simp [bernsteinIntPowerEval, certificatePolynomial, oddBUpper6Power, oddBUpper6Scale,
    mixedOddBAPower, mixedOddBBPower, mixedOddBAInt, mixedOddBBInt, Fin.sum_univ_succ,
    Finset.sum_range_succ, Vector.get, Vector.getElem_mk]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
-- Normalize the full integer coefficient table against the factored endpoint.
theorem oddBLower7_power (z k : ℝ) :
    bernsteinIntPowerEval oddBLower7Power z k =
      (oddBLower7Scale : ℝ) * mixedOddBStripLower 7 z k := by
  simp only [mixedOddBStripLower, mixed_odd_b_cleared_affine, mixedOddBStripH,
    mixed_odd_b_a_table, mixed_odd_b_b_table, certificateLogTaylor, logTwoUpper_real]
  simp [bernsteinIntPowerEval, certificatePolynomial, oddBLower7Power, oddBLower7Scale,
    mixedOddBAPower, mixedOddBBPower, mixedOddBAInt, mixedOddBBInt, Fin.sum_univ_succ,
    Finset.sum_range_succ, Vector.get, Vector.getElem_mk]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
-- Normalize the full integer coefficient table against the factored endpoint.
theorem oddBUpper7_power (z k : ℝ) :
    bernsteinIntPowerEval oddBUpper7Power z k =
      (oddBUpper7Scale : ℝ) * mixedOddBStripUpper 7 z k := by
  simp only [mixedOddBStripUpper, mixed_odd_b_cleared_affine, mixedOddBStripH,
    mixed_odd_b_a_table, mixed_odd_b_b_table, certificateLogTaylor, logTwoLower_real]
  simp [bernsteinIntPowerEval, certificatePolynomial, oddBUpper7Power, oddBUpper7Scale,
    mixedOddBAPower, mixedOddBBPower, mixedOddBAInt, mixedOddBBInt, Fin.sum_univ_succ,
    Finset.sum_range_succ, Vector.get, Vector.getElem_mk]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
-- Normalize the full integer coefficient table against the factored endpoint.
theorem oddBLower8_power (z k : ℝ) :
    bernsteinIntPowerEval oddBLower8Power z k =
      (oddBLower8Scale : ℝ) * mixedOddBStripLower 8 z k := by
  simp only [mixedOddBStripLower, mixed_odd_b_cleared_affine, mixedOddBStripH,
    mixed_odd_b_a_table, mixed_odd_b_b_table, certificateLogTaylor, logTwoUpper_real]
  simp [bernsteinIntPowerEval, certificatePolynomial, oddBLower8Power, oddBLower8Scale,
    mixedOddBAPower, mixedOddBBPower, mixedOddBAInt, mixedOddBBInt, Fin.sum_univ_succ,
    Finset.sum_range_succ, Vector.get, Vector.getElem_mk]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
-- Normalize the full integer coefficient table against the factored endpoint.
theorem oddBUpper8_power (z k : ℝ) :
    bernsteinIntPowerEval oddBUpper8Power z k =
      (oddBUpper8Scale : ℝ) * mixedOddBStripUpper 8 z k := by
  simp only [mixedOddBStripUpper, mixed_odd_b_cleared_affine, mixedOddBStripH,
    mixed_odd_b_a_table, mixed_odd_b_b_table, certificateLogTaylor, logTwoLower_real]
  simp [bernsteinIntPowerEval, certificatePolynomial, oddBUpper8Power, oddBUpper8Scale,
    mixedOddBAPower, mixedOddBBPower, mixedOddBAInt, mixedOddBBInt, Fin.sum_univ_succ,
    Finset.sum_range_succ, Vector.get, Vector.getElem_mk]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
-- Normalize the full integer coefficient table against the factored endpoint.
theorem oddBLower9_power (z k : ℝ) :
    bernsteinIntPowerEval oddBLower9Power z k =
      (oddBLower9Scale : ℝ) * mixedOddBStripLower 9 z k := by
  simp only [mixedOddBStripLower, mixed_odd_b_cleared_affine, mixedOddBStripH,
    mixed_odd_b_a_table, mixed_odd_b_b_table, certificateLogTaylor, logTwoUpper_real]
  simp [bernsteinIntPowerEval, certificatePolynomial, oddBLower9Power, oddBLower9Scale,
    mixedOddBAPower, mixedOddBBPower, mixedOddBAInt, mixedOddBBInt, Fin.sum_univ_succ,
    Finset.sum_range_succ, Vector.get, Vector.getElem_mk]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
-- Normalize the full integer coefficient table against the factored endpoint.
theorem oddBUpper9_power (z k : ℝ) :
    bernsteinIntPowerEval oddBUpper9Power z k =
      (oddBUpper9Scale : ℝ) * mixedOddBStripUpper 9 z k := by
  simp only [mixedOddBStripUpper, mixed_odd_b_cleared_affine, mixedOddBStripH,
    mixed_odd_b_a_table, mixed_odd_b_b_table, certificateLogTaylor, logTwoLower_real]
  simp [bernsteinIntPowerEval, certificatePolynomial, oddBUpper9Power, oddBUpper9Scale,
    mixedOddBAPower, mixedOddBBPower, mixedOddBAInt, mixedOddBBInt, Fin.sum_univ_succ,
    Finset.sum_range_succ, Vector.get, Vector.getElem_mk]
  ring

end EulerDipoleEigenvalues
