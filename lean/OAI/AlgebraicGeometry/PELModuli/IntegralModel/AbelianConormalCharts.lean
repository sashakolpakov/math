import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.ConormalAction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData

/-! # Abelian Conormal Charts -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.AbelianConormalCharts

noncomputable section

/-! The simultaneous conormal charts are constructed for the actual
unit section and any finite list of endomorphisms in an integral action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  {R I : Type} [CommRing R] (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A) (a : I → R)

theorem abelian_unit_section : η[A.scheme].left ≫ A.scheme.hom = 𝟙 S := η[A.scheme].w

theorem action_over (i : I) : (ρ.map (a i)).left ≫ A.scheme.hom = A.scheme.hom := (ρ.map (a i)).w

theorem action_unit_section (i : I) :
    η[A.scheme].left ≫ (ρ.map (a i)).left = η[A.scheme].left :=
  congrArg Over.Hom.left (IsMonHom.one_hom (ρ.map (a i)))

theorem exists_abelian_conormal_chart [Finite I] (x : S) :
    ∃ C : Section.ActionCharts.SectionMorphismChart A.scheme.hom η[A.scheme].left (fun i => (ρ.map (a i)).left),
      x ∈ C.V :=
  Section.ActionCharts.exists_sectionMorphismChart A.scheme.hom η[A.scheme].left (abelian_unit_section A)
    (fun i => (ρ.map (a i)).left) (action_over A ρ a) (action_unit_section A ρ a) x

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.AbelianConormalCharts
