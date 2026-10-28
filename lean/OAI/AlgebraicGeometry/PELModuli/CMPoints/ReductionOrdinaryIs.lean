import OAI.AlgebraicGeometry.PELModuli.CMPoints.OrdinaryFiberCount

/-! # Reduction Ordinary Is -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints

noncomputable section

/-! The proved height-one criterion implies precisely the ordinary
condition on a geometric reduction point. All scalar and fiber maps
are those already constructed in the integral PEL model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {M : Models.RankThreePELModel E K} {q : ℕ} [Fact q.Prime]
  {j : M.QadicChoice q} (R : M.GoodIntegralReduction q j)

instance Models.RankThreePELModel.GoodIntegralReduction.fiberField_charP (a : M.Family) (x : R.geom a) : CharP (R.fiberField a x) q :=
  CharP.of_ringHom_of_ne_zero (R.fiberScalar a x) q (Fact.out : q.Prime).ne_zero

theorem Models.RankThreePELModel.GoodIntegralReduction.isOrdinary_of_torsion_heightOne_decomposition
    (a : M.Family) (x : R.geom a) {I : Type} [Fintype I]
    (G : I → GroupSchemes.FiniteEtale.PDivisibleGroup (R.fiberField a x) q 1)
    (hI : Fintype.card I = 2 * (3 * M.s))
    (e : (R.fiberAbelian a x).torsionFunctor q ≅
      FlattenTorsionFactors.piGroupFunctor (fun i => OrdinaryFromFactors.finiteGroupPointFunctor ((G i).level 1))) :
    R.IsOrdinary a x := by
  have hgood : q.Coprime (∏ i, (M.datum a).polarizationType i) :=
    (R.polarizationPrimeToQ a).of_dvd_right (dvd_pow_self _ (by decide : 2 ≠ 0))
  have hcount := OrdinaryFromFactors.ordinary_count_of_torsion_heightOne_decomposition
    (R.fiberPolarized a x) hgood G hI e
  exact (OrdinaryFiberCount.isOrdinaryAt_iff_geometricFiber_count (R.abelian a) x).mpr hcount

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints
