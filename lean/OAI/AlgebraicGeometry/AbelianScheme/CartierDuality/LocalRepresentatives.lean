import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SliceRepresentabilityIs
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RelativeRepresentabilityP

/-! # Local Representatives -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LocalRepresentatives

noncomputable section

/-!
# CartierDuality: local representatives over open base schemes
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonoidalCategory

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.Schemes

/-- A representative of the restriction of a presheaf to an open base
piece defines a relatively representable open immersion into that presheaf. -/
theorem sliceRepresentative_isOpen {S : Scheme.{u}} {U : Over S}
    [IsOpenImmersion U.hom] {F : (Over S)ᵒᵖ ⥤ Type u} {Y : Over U}
    (r : ((Over.forget U).op ⋙ F).RepresentableBy Y) :
    (RelativeRepresentabilityP.Construction.Schemes.relativeOpenImmersion S).presheaf (SliceRepresentabilityIs.Construction.SliceRepresentability.canonicalMap r) := by
  apply SliceRepresentabilityIs.Construction.SliceRepresentability.canonicalMap_relative r (RelativeRepresentabilityP.Construction.Schemes.relativeOpenImmersion S)
  intro X
  change IsOpenImmersion (Limits.pullback.fst X.hom U.hom)
  infer_instance

/-- A sheaf over a scheme is representable if its restrictions over
an open cover of the base are representable. -/
theorem isRepresentable_of_openCover {S : Scheme.{u}}
    (F : Sheaf (Scheme.zariskiTopology.over S) (Type u)) (𝒰 : Scheme.OpenCover.{u} S)
    (h : ∀ i, ((Over.forget (Over.mk (𝒰.f i))).op ⋙ F.obj).IsRepresentable) :
    F.obj.IsRepresentable := by
  let U (i : 𝒰.I₀) : Over S := Over.mk (𝒰.f i)
  let (i : 𝒰.I₀) : IsOpenImmersion (U i).hom :=
    inferInstanceAs (IsOpenImmersion (𝒰.f i))
  let (i : 𝒰.I₀) : ((Over.forget (U i)).op ⋙ F.obj).IsRepresentable := h i
  let Y (i : 𝒰.I₀) := ((Over.forget (U i)).op ⋙ F.obj).reprX
  let r (i : 𝒰.I₀) := ((Over.forget (U i)).op ⋙ F.obj).representableBy
  have hcover : Sieve.ofArrows U (fun i => toUnit (U i)) ∈
      (Scheme.zariskiTopology.over S) (𝟙_ (Over S)) := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact 𝒰.mem_grothendieckTopology
  let : Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over S)
      (Sigma.desc (fun i => SliceRepresentabilityIs.Construction.SliceRepresentability.canonicalMap (r i))) :=
    SliceRepresentabilityIs.Construction.SliceRepresentability.canonicalMaps_locallySurjective (Scheme.zariskiTopology.over S)
      U Y r hcover
  exact RelativeRepresentabilityP.Construction.Schemes.RelativeRepresentability.isRepresentable F
    (fun i => SliceRepresentabilityIs.Construction.SliceRepresentability.canonicalMap (r i))
    (fun i => sliceRepresentative_isOpen (r i))

end Construction.Schemes

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LocalRepresentatives
