import NoEmbeddedEigenvalues.PhaseCellDivision

/-!
# Scalar interfaces for phase-cell division

Quarter scalars are defined in `QuarterScalars.lean`, complete-cell estimates in
`PhaseCellEstimates.lean`, and their global assembly in `PhaseCellDivision.lean`.

Endpoint Hardy uses the primitive averaging mechanism in `HardyAverage.lean`;
second-order division uses H¹ segment averaging in `IntervalSegmentAverage.lean`.
Endpoints always mean canonical H¹ traces. Local H² data use specified first and
second derivatives, and hence actual continuous numerator values at interior resonances.

The phase-cell estimates export uniform constants on complete cells. This quantitative
interface, not merely qualitative unweighted division, is what logarithmic weighted
summation uses. All four quarter characters are allowed. Angular Hardy is not part
of these interfaces and is not required by the odd–odd quotient route.
-/
