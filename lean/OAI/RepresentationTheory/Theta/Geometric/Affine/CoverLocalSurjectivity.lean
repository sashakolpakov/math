import OAI.RepresentationTheory.Theta.Geometric.FppfPicardLocality
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! # Cover Local Surjectivity -/

namespace OAI.RepresentationTheory.Theta.Geometric.Affine.CoverLocalSurjectivity

noncomputable section

/-! A locally presented section lifts locally if all its affine
restrictions lift. The covering is the actual affine scheme cover. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v
variable {S : Scheme.{u}}

theorem affineCover_over_mem (T : Over S) :
    Sieve.ofArrows
      (fun i => Over.mk (T.left.affineCover.f i ≫ T.hom))
      (fun i => Over.homMk (T.left.affineCover.f i) (by rfl)) ∈
        (Scheme.fppfTopology.over S) T := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact (Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage)
    _ T.left.affineCover.mem_grothendieckTopology

theorem locallySurjective_of_affine_representatives
    {F P G : (Over S)ᵒᵖ ⥤ Type v} (f : F ⟶ G) (g : P ⟶ G)
    [Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) g]
    (h : ∀ (T : Over S) [IsAffine T.left] (x : P.obj (.op T)),
      ∃ y : F.obj (.op T), f.app (.op T) y = g.app (.op T) x) :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) f where
  imageSieve_mem {T} s := by
    let J := Scheme.fppfTopology.over S
    apply J.transitive (Presheaf.imageSieve_mem J g s) (Presheaf.imageSieve f s)
    intro U j hj
    obtain ⟨x, hx⟩ := hj
    apply J.superset_covering ((Sieve.generate_le_iff _ _).mpr ?_) (affineCover_over_mem U)
    intro V' v' hv
    obtain ⟨i⟩ := hv
    let V := Over.mk (U.left.affineCover.f i ≫ U.hom)
    let v : V ⟶ U := Over.homMk (U.left.affineCover.f i) (by rfl)
    let : IsAffine V.left := inferInstanceAs (IsAffine (U.left.affineCover.X i))
    obtain ⟨y, hy⟩ := h V (P.map v.op x)
    refine ⟨y, ?_⟩
    change f.app (.op V) y = G.map (v ≫ j).op s
    rw [hy, g.naturality_apply, hx, op_comp, Functor.map_comp_apply]

end

end OAI.RepresentationTheory.Theta.Geometric.Affine.CoverLocalSurjectivity
