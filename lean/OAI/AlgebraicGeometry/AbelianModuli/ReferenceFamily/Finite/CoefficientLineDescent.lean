import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.InverseLimit.LineDescent
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.CoefficientFrames

/-! # Coefficient Line Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.CoefficientLineDescent

noncomputable section

/-! Every actual line bundle on a constant proper family over an
arbitrary coefficient algebra has an actual finite-coefficient model. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory

variable (k R : Type) [CommRing k] [CommRing R] [Algebra k R]

instance finiteCoefficientFamily_affineDiagonal (X : Over (Spec (.of k))) [IsSeparated X.hom]
    (s : (Finset R)ᵒᵖ) :
    IsAffineHom (pullback.diagonal (terminal.from ((CoefficientFrames.finiteCoefficientFamilyDiagram k R X).obj s))) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap k (CoefficientDiagram.finiteCoefficientRing k R s.unop)))
  change IsAffineHom (pullback.diagonal (terminal.from (pullback f X.hom)))
  let : IsSeparated (pullback.fst f X.hom) := inferInstance
  let : IsSeparated (terminal.from (Spec (.of (CoefficientDiagram.finiteCoefficientRing k R s.unop)))) := inferInstance
  have h : IsSeparated (pullback.fst f X.hom ≫ terminal.from (Spec (.of (CoefficientDiagram.finiteCoefficientRing k R s.unop)))) :=
    inferInstance
  have he : pullback.fst f X.hom ≫ terminal.from (Spec (.of (CoefficientDiagram.finiteCoefficientRing k R s.unop))) =
      terminal.from (pullback f X.hom) := Subsingleton.elim _ _
  let : IsSeparated (terminal.from (pullback f X.hom)) := he ▸ h
  infer_instance

theorem exists_finite_coefficient_line_model [IsNoetherianRing k]
    (X : Over (Spec (.of k))) [IsProper X.hom]
    (L : HilbertConstruction.Line.Bundles.LineBundle (CoefficientLimit.algebraSpecOver k R ⊗ X).left) :
    ∃ (s : Finset R) (K : HilbertConstruction.Line.Bundles.LineBundle ((CoefficientFrames.finiteCoefficientFamilyDiagram k R X).obj (.op s))),
      Nonempty ((K.pullback ((CoefficientLimit.finiteCoefficientFamilyCone k R X).π.app (.op s))).sheaf ≅ L.sheaf) := by
  classical
  obtain ⟨i, K, hK⟩ := InverseLimit.LineDescent.exists_limit_line_stage (CoefficientFrames.finiteCoefficientFamilyDiagram k R X)
    (CoefficientLimit.finiteCoefficientFamilyCone k R X) (CoefficientLimit.finiteCoefficientFamilyCone_isLimit k R X) L
  exact ⟨i.unop, K, hK⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.CoefficientLineDescent
