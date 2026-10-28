import OAI.AlgebraicGeometry.Crystalline.Cohomology.DerivedVanishing

/-! # Empty Frame -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.EmptyFrame.CrystallineEmptyFrame

noncomputable section

/-!
# A coordinate-free frame and the native structure sheaf

For an empty coordinate type the coefficient inclusion is an isomorphism:
the already constructed successive projection for the empty list is the
identity. Degree-zero tensor forms identify with frame functions. After
the prescribed coefficient lift and sheafification this identifies the
actual degree-zero frame term with the original native structure sheaf.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped TensorProduct

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B) [Fintype σ]

local notation "W" => WittVector p k
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k X

def termZeroIso : (CrystallineFrame.Resolution.CrystallineFrameResolution.complex p k B σ a).X 0 ≅
    CrystallineFrame.Operators.CrystallineFrameOperators.functions p k B σ a :=
  NatIso.ofComponents
    (fun Q => (TensorDegree.TensorDegreeZero.equiv W σ
      ((CrystallineFrame.Operators.CrystallineFrameOperators.functions p k B σ a).obj Q)).toModuleIso)
    (by
      intro Q P f
      apply ModuleCat.hom_ext
      apply TensorProduct.ext
      apply LinearMap.ext
      intro m
      apply LinearMap.ext
      intro ω
      change TensorDegree.TensorDegreeZero.equiv W σ ((CrystallineFrame.Operators.CrystallineFrameOperators.functions p k B σ a).obj P)
        (((CrystallineFrame.Operators.CrystallineFrameOperators.functions p k B σ a).map f).hom m ⊗ₜ[W] ω) =
          ((CrystallineFrame.Operators.CrystallineFrameOperators.functions p k B σ a).map f).hom
            (TensorDegree.TensorDegreeZero.equiv W σ ((CrystallineFrame.Operators.CrystallineFrameOperators.functions p k B σ a).obj Q) (m ⊗ₜ[W] ω))
      exact (((CrystallineFrame.Operators.CrystallineFrameOperators.functions p k B σ a).map f).hom.map_smul
        (exteriorPower.zeroEquiv W (σ →₀ W) ω) m).symm)

variable [IsEmpty σ]

omit [Fintype σ] in
theorem coefficient_isIso (Q : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)) :
    IsIso ((CrystallineFrame.Operators.CrystallineFrameOperators.coefficients p k B σ a).app (op Q)) := by
  refine ⟨⟨ModuleCat.ofHom (CrystallineFrame.Operators.CrystallineFrameOperators.retraction p k B σ a (op Q)), ?_, ?_⟩⟩
  · apply ModuleCat.hom_ext
    exact CrystallineFrame.Resolution.CrystallineFrameResolution.coefficient_split p k B σ a (op Q)
  · apply ModuleCat.hom_ext
    exact (CrystallineFrame.Resolution.CrystallineFrameResolution.finalProjection p k B σ a (op Q) []
      (fun i => isEmptyElim i)).symm

def functionsIso : Site.functions p k X ≅ CrystallineFrame.Operators.CrystallineFrameOperators.functions p k B σ a := by
  have : ∀ Q, IsIso ((CrystallineFrame.Operators.CrystallineFrameOperators.coefficients p k B σ a).app Q) :=
    fun Q => coefficient_isIso p k B σ a Q.unop
  have : IsIso (CrystallineFrame.Operators.CrystallineFrameOperators.coefficients p k B σ a) := NatIso.isIso_of_isIso_app _
  exact asIso (CrystallineFrame.Operators.CrystallineFrameOperators.coefficients p k B σ a)

def sheafZeroIso : (CrystallineFrame.SheafResolution.CrystallineFrameSheafResolution.complex p k B σ a).X 0 ≅
    Site.structureSheaf p k X :=
  (PolynomialSheafResolution.CrystallinePolynomialSheafResolution.toSheaf p k X).mapIso
    (termZeroIso p k B σ a ≪≫ (functionsIso p k B σ a).symm) ≪≫
      PolynomialSheafResolution.CrystallinePolynomialSheafResolution.coefficientIso p k X

omit [Fintype σ] [IsEmpty σ] in
theorem structure_acyclic : CrystallineCech.CechAcyclic.CrystallineCechAcyclic.Acyclic p k X (Site.structureSheaf p k X) := by
  let emptyCoordinates : PEmpty.{u + 1} → B := PEmpty.elim
  exact CrystallineCech.CechAcyclic.CrystallineCechAcyclic.of_iso p k X
    (CrystallineCech.CechAcyclic.CrystallineCechAcyclic.frame p k B PEmpty.{u + 1} emptyCoordinates 0)
      (sheafZeroIso p k B PEmpty.{u + 1} emptyCoordinates)

omit [Fintype σ] [IsEmpty σ] in
theorem structure_derived_isZero
    (Q : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B))
    (n : ℕ) (hn : n ≠ 0) :
    IsZero (DerivedEvaluation.CrystallineDerivedEvaluation.cohomology p k X (Site.structureSheaf p k X) Q n) :=
  DerivedVanishing.CrystallineDerivedVanishing.isZero p k X _ (structure_acyclic p k B) Q n hn

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.EmptyFrame.CrystallineEmptyFrame
