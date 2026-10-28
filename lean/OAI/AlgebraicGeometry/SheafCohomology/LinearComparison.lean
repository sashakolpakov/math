import OAI.AlgebraicGeometry.SheafCohomology.AffineComparison
import OAI.AlgebraicGeometry.SheafCohomology.ExtNaturality
import OAI.AlgebraicGeometry.SheafCohomology.Scalars

/-! # Linear Comparison -/

namespace OAI.AlgebraicGeometry.SheafCohomology.LinearComparison.Projective

noncomputable section

/-! Additive and scalar compatibility of ProjectiveCohomology's cohomology comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian _root_.TopologicalSpace

local instance (X : TopCat.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)) :=
  HasExt.standard _
local instance (X : TopCat.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℤ)) :=
  HasExt.standard _
local instance (X : TopCat.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- The coefficient comparison is an equivalence of abelian groups. -/
def complexSheafCohomologyAddEquiv (X : TopCat.{0})
    (N : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)) (n : ℕ) :
    Ext.{1} ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).obj
      (ModuleCat.of ℂ ℂ)) N n ≃+
      Sheaf.H.{0} ((IntegerCoefficients.Projective.integerSheafForget X).obj ((Coefficients.Projective.restrictComplexSheaf X).obj N)) n := by
  let I := (constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)
  let NAb := (IntegerCoefficients.Projective.integerSheafForget X).obj ((Coefficients.Projective.restrictComplexSheaf X).obj N)
  exact (ExtLeft.Projective.extLeftIso (ConstantCoefficients.Projective.extendConstantComplexIso X).symm N n).trans
    (Coefficients.Projective.complexSheafExtAdjunction X I N n) |>.trans
    (IntegerCoefficients.Projective.integerSheafExtEquiv X I ((Coefficients.Projective.restrictComplexSheaf X).obj N) n) |>.trans
    (ExtLeft.Projective.extLeftIso (ConstantCoefficients.Projective.forgetConstantIntegerIso X ≪≫ ConstantCoefficients.Projective.constantIntegerUliftIso X) NAb n)
      |>.trans (ExtNaturality.Projective.extChangeUniverseAddEquiv _ _ n)

@[simp] theorem complexSheafCohomologyAddEquiv_apply (X : TopCat.{0})
    (N : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)) (n : ℕ)
    (x : Ext.{1} ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).obj
      (ModuleCat.of ℂ ℂ)) N n) :
    complexSheafCohomologyAddEquiv X N n x = CoherentVanishing.Projective.complexSheafCohomologyEquiv X N n x := rfl

theorem complexSheafCohomologyAddEquiv_naturality (X : TopCat.{0})
    {M N : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)}
    (f : M ⟶ N) (n : ℕ)
    (x : Ext.{1} ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).obj
      (ModuleCat.of ℂ ℂ)) M n) :
    complexSheafCohomologyAddEquiv X N n (x.comp (Ext.mk₀ f) (Nat.add_zero n)) =
      (complexSheafCohomologyAddEquiv X M n x).comp
        (Ext.mk₀ ((IntegerCoefficients.Projective.integerSheafForget X).map ((Coefficients.Projective.restrictComplexSheaf X).map f)))
        (Nat.add_zero n) := by
  simp only [complexSheafCohomologyAddEquiv, AddEquiv.trans_apply,
    ExtNaturality.Projective.extLeftIso_naturality, Coefficients.Projective.complexSheafExtAdjunction, ExtAdjunction.Projective.extAdjunction,
    AddEquiv.ofBijective_apply, ExtNaturality.Projective.extCompare_naturality, IntegerCoefficients.Projective.integerSheafExtEquiv,
    Functor.mapExtAddHom_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    ExtNaturality.Projective.extChangeUniverse_comp_mk₀]

/-- The actual complex Ext groups and Zariski cohomology are linearly equivalent
for the canonical action induced by the complex structure morphism. -/
def coherentCohomologyLinearEquivZariski (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (M : A.carrier.Modules) (n : ℕ) :
    letI := Scalars.Projective.zariskiComplexCohomologyModule A M n
    Sheaves.Projective.coherentCohomology A M n ≃ₗ[ℂ] AffineH.Projective.H M n := by
  letI := Scalars.Projective.zariskiComplexCohomologyModule A M n
  refine { complexSheafCohomologyAddEquiv (TopCat.of A.carrier) (Sheaves.Projective.complexSheaf A M) n
    with map_smul' := ?_ }
  intro r x
  have h := complexSheafCohomologyAddEquiv_naturality (TopCat.of A.carrier)
    (r • 𝟙 (Sheaves.Projective.complexSheaf A M)) n x
  rw [Scalars.Projective.forgetComplexScalarHom] at h
  exact (congrArg (fun y => complexSheafCohomologyAddEquiv
    (TopCat.of A.carrier) (Sheaves.Projective.complexSheaf A M) n y)
      (Ext.smul_eq_comp_mk₀ x r)).trans h

/-- The two actual cohomology constructions have identical complex dimensions. -/
theorem coherentCohomology_finrank_eq_zariski (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (M : A.carrier.Modules) (n : ℕ) :
    letI := Scalars.Projective.zariskiComplexCohomologyModule A M n
    Module.finrank ℂ (Sheaves.Projective.coherentCohomology A M n) = Module.finrank ℂ (AffineH.Projective.H M n) := by
  let := Scalars.Projective.zariskiComplexCohomologyModule A M n
  exact (coherentCohomologyLinearEquivZariski A M n).finrank_eq

end

end OAI.AlgebraicGeometry.SheafCohomology.LinearComparison.Projective
