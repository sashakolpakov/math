import OAI.AlgebraicGeometry.SheafCohomology.ConstantCoefficients
import OAI.AlgebraicGeometry.SheafCohomology.ExtNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.AffineAcyclicity

/-! # Sheaf Cohomology -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Complex.SheafCohomology

noncomputable section

/-! Forgetting complex coefficients preserves actual form-sheaf cohomology and affine vanishing. -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian _root_.AlgebraicGeometry _root_.TopologicalSpace

local instance complexSheavesExt (X : TopCat.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)) := HasExt.standard _

local instance integerSheavesExt (X : TopCat.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℤ)) := HasExt.standard _

local instance additiveSheavesExt (X : TopCat.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

theorem complexExtAdjunction_naturality (X : TopCat.{0})
    (P : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℤ))
    {M N : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)} (f : M ⟶ N) (q : ℕ)
    (x : Ext.{1} ((SheafCohomology.Coefficients.Projective.extendComplexSheaf X).obj P) M q) :
    SheafCohomology.Coefficients.Projective.complexSheafExtAdjunction X P N q (x.comp (Ext.mk₀ f) (Nat.add_zero q)) =
      (SheafCohomology.Coefficients.Projective.complexSheafExtAdjunction X P M q x).comp
        (Ext.mk₀ ((SheafCohomology.Coefficients.Projective.restrictComplexSheaf X).map f)) (Nat.add_zero q) :=
  SheafCohomology.ExtNaturality.Projective.extCompare_naturality (SheafCohomology.Coefficients.Projective.restrictComplexSheaf X) P
    ((SheafCohomology.Coefficients.Projective.extendComplexSheaf X).obj P) ((SheafCohomology.Coefficients.Projective.complexSheafAdjunction X).unit.app P)
    f q x

theorem integerExtEquiv_naturality (X : TopCat.{0})
    (P : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℤ))
    {M N : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℤ)} (f : M ⟶ N) (q : ℕ)
    (x : Ext.{1} P M q) :
    SheafCohomology.IntegerCoefficients.Projective.integerSheafExtEquiv X P N q (x.comp (Ext.mk₀ f) (Nat.add_zero q)) =
      (SheafCohomology.IntegerCoefficients.Projective.integerSheafExtEquiv X P M q x).comp
        (Ext.mk₀ ((SheafCohomology.IntegerCoefficients.Projective.integerSheafForget X).map f)) (Nat.add_zero q) := by
  change (x.comp (Ext.mk₀ f) (Nat.add_zero q)).mapExactFunctor (SheafCohomology.IntegerCoefficients.Projective.integerSheafForget X) =
    (x.mapExactFunctor (SheafCohomology.IntegerCoefficients.Projective.integerSheafForget X)).comp
      (Ext.mk₀ ((SheafCohomology.IntegerCoefficients.Projective.integerSheafForget X).map f)) (Nat.add_zero q)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]

def complexSheafCohomologyForgetEquiv (X : TopCat.{0})
    (N : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)) (q : ℕ) :
    Ext.{1} ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).obj
      (ModuleCat.of ℂ ℂ)) N q ≃+
      Sheaf.H.{0} ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj N) q := by
  let I := (constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)
  let NAb := (SheafCohomology.IntegerCoefficients.Projective.integerSheafForget X).obj ((SheafCohomology.Coefficients.Projective.restrictComplexSheaf X).obj N)
  exact (SheafCohomology.ExtLeft.Projective.extLeftIso (SheafCohomology.ConstantCoefficients.Projective.extendConstantComplexIso X).symm N q).trans
    (SheafCohomology.Coefficients.Projective.complexSheafExtAdjunction X I N q) |>.trans
    (SheafCohomology.IntegerCoefficients.Projective.integerSheafExtEquiv X I ((SheafCohomology.Coefficients.Projective.restrictComplexSheaf X).obj N) q) |>.trans
    (SheafCohomology.ExtLeft.Projective.extLeftIso
      (SheafCohomology.ConstantCoefficients.Projective.forgetConstantIntegerIso X ≪≫ SheafCohomology.ConstantCoefficients.Projective.constantIntegerUliftIso X) NAb q)
      |>.trans (SheafCohomology.ExtNaturality.Projective.extChangeUniverseAddEquiv _ _ q)

theorem complexSheafCohomologyForgetEquiv_naturality (X : TopCat.{0})
    {M N : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)} (f : M ⟶ N) (q : ℕ)
    (x : Ext.{1} ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).obj
      (ModuleCat.of ℂ ℂ)) M q) :
    complexSheafCohomologyForgetEquiv X N q (x.comp (Ext.mk₀ f) (Nat.add_zero q)) =
      (complexSheafCohomologyForgetEquiv X M q x).comp
        (Ext.mk₀ ((sheafCompose (Opens.grothendieckTopology X)
          (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).map f)) (Nat.add_zero q) := by
  let I := (constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)
  let R := SheafCohomology.Coefficients.Projective.restrictComplexSheaf X
  let G := SheafCohomology.IntegerCoefficients.Projective.integerSheafForget X
  let a (T : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)) :=
    SheafCohomology.ExtLeft.Projective.extLeftIso (SheafCohomology.ConstantCoefficients.Projective.extendConstantComplexIso X).symm T q
  let b (T : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)) :=
    SheafCohomology.Coefficients.Projective.complexSheafExtAdjunction X I T q
  let c (T : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)) :=
    SheafCohomology.IntegerCoefficients.Projective.integerSheafExtEquiv X I (R.obj T) q
  let e := SheafCohomology.ConstantCoefficients.Projective.forgetConstantIntegerIso X ≪≫ SheafCohomology.ConstantCoefficients.Projective.constantIntegerUliftIso X
  let d (T : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)) :=
    SheafCohomology.ExtLeft.Projective.extLeftIso e (G.obj (R.obj T)) q
  let v (T : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)) :=
    SheafCohomology.ExtNaturality.Projective.extChangeUniverseAddEquiv.{1, 0, 1, 0}
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of (ULift.{0} ℤ))) (G.obj (R.obj T)) q
  have h₁ := SheafCohomology.ExtNaturality.Projective.extLeftIso_naturality
    (SheafCohomology.ConstantCoefficients.Projective.extendConstantComplexIso X).symm f q x
  have h₂ := complexExtAdjunction_naturality X I f q (a M x)
  have h₃ := integerExtEquiv_naturality X I (R.map f) q (b M (a M x))
  have h₄ := SheafCohomology.ExtNaturality.Projective.extLeftIso_naturality e (G.map (R.map f)) q (c M (b M (a M x)))
  have h₅ := SheafCohomology.ExtNaturality.Projective.extChangeUniverse_comp_mk₀.{1, 0, 1, 0} q
    (d M (c M (b M (a M x)))) (G.map (R.map f))
  change v N (d N (c N (b N (a N (x.comp (Ext.mk₀ f) (Nat.add_zero q)))))) = _
  calc
    _ = v N (d N (c N (b N ((a M x).comp (Ext.mk₀ f) (Nat.add_zero q))))) :=
      congrArg (fun z => v N (d N (c N (b N z)))) h₁
    _ = v N (d N (c N ((b M (a M x)).comp (Ext.mk₀ (R.map f)) (Nat.add_zero q)))) :=
      congrArg (fun z => v N (d N (c N z))) h₂
    _ = v N (d N ((c M (b M (a M x))).comp (Ext.mk₀ (G.map (R.map f))) (Nat.add_zero q))) :=
      congrArg (fun z => v N (d N z)) h₃
    _ = v N ((d M (c M (b M (a M x)))).comp (Ext.mk₀ (G.map (R.map f))) (Nat.add_zero q)) :=
      congrArg (v N) h₄
    _ = _ := h₅

theorem smooth_affine_algebraicFormExt_acyclic (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [Smooth X.hom] [IsAffine X.left] (n q : ℕ) :
    Subsingleton (Ext.{1} (Algebraic.Sheaves.constantComplexSheaf X) ((Algebraic.Sheaves.algebraicDeRhamSheafComplex X).X n) (q + 1)) :=
  (complexSheafCohomologyForgetEquiv (TopCat.of X.left)
    ((Algebraic.Sheaves.algebraicDeRhamSheafComplex X).X n) (q + 1)).toEquiv.subsingleton_congr.mpr
      (Betti.Smooth.AffineAcyclicity.smooth_algebraicForms_acyclic X n q)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Complex.SheafCohomology
