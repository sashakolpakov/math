import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineCompactificationOf
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineCover
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperProduct
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GraphClosureIs
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackEmbeddingOf
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ChowEmbeddingClosed

/-! # Chow Modification Model -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ChowModificationModel.Construction.ChowModification

noncomputable section

/-! Chow's construction for a proper integral scheme over a Noetherian
affine base, embedded in a finite product of explicit projective closures. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

structure Model (f : X ⟶ Spec (.of R)) where
  cover : AffineCover.Construction.FiniteAffineCover.Data X
  compactification : ∀ i, AffineCompactificationOf.Construction.AffineCompactification.Data ((cover.opens i).ι ≫ f)
  scheme : Scheme.{u}
  integral : IsIntegral scheme
  projection : scheme ⟶ X
  proper : IsProper projection
  surjective : Surjective projection
  isIso_restrict : IsIso (projection ∣_ cover.common)
  embedding : scheme ⟶
    (ProperProduct.Construction.FiniteProperProduct.product (fun i => Over.mk (compactification i).base)).left
  closedImmersion : IsClosedImmersion embedding
  embedding_base : embedding ≫
      (ProperProduct.Construction.FiniteProperProduct.product (fun i => Over.mk (compactification i).base)).hom =
    projection ≫ f

def build [IsNoetherianRing R] [IsIntegral X] (f : X ⟶ Spec (.of R)) [IsProper f] : Model f := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let C := AffineCover.Construction.FiniteAffineCover.ofIntegral X
  let D (i : Fin C.n) : AffineCompactificationOf.Construction.AffineCompactification.Data ((C.opens i).ι ≫ f) := by
    have : IsAffine (C.opens i).toScheme := C.affine i
    exact AffineCompactificationOf.Construction.AffineCompactification.ofFiniteType ((C.opens i).ι ≫ f)
  let P : Fin C.n → Over (Spec (.of R)) := fun i => Over.mk (D i).base
  let B := ProperProduct.Construction.FiniteProperProduct.product P
  have : IsProper B.hom := ProperProduct.Construction.FiniteProperProduct.proper P (fun i => (D i).proper)
  have : Nonempty C.common := C.common_nonempty
  have : IsAffine C.common.toScheme := C.common_affine
  let T := Over.mk (C.common.ι ≫ f)
  let a (i : Fin C.n) : T ⟶ P i :=
    Over.homMk (X.homOfLE (C.common_le i) ≫ (D i).chart) (by
      change (X.homOfLE (C.common_le i) ≫ (D i).chart) ≫ (D i).base = C.common.ι ≫ f
      rw [Category.assoc, (D i).chart_base, ← Category.assoc, X.homOfLE_ι])
  let j := (ProperProduct.Construction.FiniteProperProduct.lift P a).left
  have hj : C.common.ι ≫ f = j ≫ B.hom := (Over.w (ProperProduct.Construction.FiniteProperProduct.lift P a)).symm
  let Z := GraphClosureIs.Construction.GraphClosure.scheme f B.hom C.common j hj
  let q := GraphClosureIs.Construction.GraphClosure.projection f B.hom C.common j hj
  let g := GraphClosureIs.Construction.GraphClosure.map f B.hom C.common j hj
  let t := GraphClosureIs.Construction.GraphClosure.chart f B.hom C.common j hj
  have hZ : IsIntegral Z := GraphClosureIs.Construction.GraphClosure.integral f B.hom C.common j hj
  have hq : IsProper q := GraphClosureIs.Construction.GraphClosure.proper f B.hom C.common j hj
  have hg : IsProper g := GraphClosureIs.Construction.GraphClosure.map_isProper f B.hom C.common j hj
  have ht : IsDominant t := GraphClosureIs.Construction.GraphClosure.dominant f B.hom C.common j hj
  have hpair : IsClosedImmersion (prod.lift q g) :=
    PullbackEmbeddingOf.Construction.PullbackEmbedding.pair_of_closed f B.hom (GraphClosureIs.Construction.GraphClosure.graph f B.hom C.common j hj).imageι
  have hsep (i : Fin C.n) : (D i).scheme.IsSeparated := by
    have : IsProper (D i).base := (D i).proper
    exact ⟨by rw [← terminal.comp_from (D i).base]; infer_instance⟩
  have hopen (i : Fin C.n) : IsOpenImmersion (D i).chart := (D i).openImmersion
  have hclosed : IsClosedImmersion g := by
    apply ChowEmbeddingClosed.Construction.ChowEmbedding.closed q g C.opens C.covers (fun i => (D i).scheme)
      (fun i => (D i).chart) (fun i => (ProperProduct.Construction.FiniteProperProduct.projection P i).left)
      t (fun i => X.homOfLE (C.common_le i))
    · intro i
      exact (GraphClosureIs.Construction.GraphClosure.chart_projection f B.hom C.common j hj).trans (X.homOfLE_ι _).symm
    · intro i
      change GraphClosureIs.Construction.GraphClosure.chart f B.hom C.common j hj ≫
        GraphClosureIs.Construction.GraphClosure.map f B.hom C.common j hj ≫ (ProperProduct.Construction.FiniteProperProduct.projection P i).left = _
      rw [← Category.assoc, GraphClosureIs.Construction.GraphClosure.chart_map]
      exact congrArg Over.Hom.left (ProperProduct.Construction.FiniteProperProduct.lift_projection P a i)
  exact ⟨C, D, Z, hZ, q, hq, GraphClosureIs.Construction.GraphClosure.surjective f B.hom C.common j hj,
    GraphClosureIs.Construction.GraphClosure.isIso_restrict f B.hom C.common j hj, g, hclosed,
    GraphClosureIs.Construction.GraphClosure.map_base f B.hom C.common j hj⟩

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ChowModificationModel.Construction.ChowModification
