import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EtaleTargetMaps

/-! # Affine Special Fiber -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.AffineSpecialFiber.Components

noncomputable section

/-!
The coordinate tensor product agrees with the native special-fiber
functor on objects and maps. This lets HenselianLifting construct scheme maps from
their independently specified special fibers.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped TensorProduct

universe u

variable (R S A : Type u) [CommRing R] [CommRing S] [CommRing A]
variable [Algebra R S] [Algebra R A]

def affineBaseChangeIso :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj (EtaleTargetMaps.Components.affineOver R A) ≅
      EtaleTargetMaps.Components.affineOver S (S ⊗[R] A) :=
  (pullbackSymmetry .. ≪≫ pullbackSpecIso' R S A).asOver (Spec (.of S))

theorem affineBaseChangeIso_inv_fst :
    (affineBaseChangeIso R S A).inv.left ≫
      pullback.fst (EtaleTargetMaps.Components.affineOver R A).hom (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom) := by
  change (pullbackSpecIso' R S A).inv ≫ (pullbackSymmetry _ _).inv ≫ pullback.fst _ _ = _
  rw [pullbackSymmetry_inv_comp_fst]
  exact pullbackSpecIso_inv_snd R S A

variable {A} {C : Type u} [CommRing C] [Algebra R C]

theorem affineBaseChangeIso_naturality (f : C →ₐ[R] A) :
    (affineBaseChangeIso R S A).inv ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map (EtaleTargetMaps.Components.affineMap R f) =
    EtaleTargetMaps.Components.affineMap S (Algebra.TensorProduct.map (AlgHom.id S S) f) ≫
      (affineBaseChangeIso R S C).inv := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc]
    have hp :
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map
          (EtaleTargetMaps.Components.affineMap R f)).left ≫
          pullback.fst (EtaleTargetMaps.Components.affineOver R C).hom (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
        pullback.fst (EtaleTargetMaps.Components.affineOver R A).hom (Spec.map (CommRingCat.ofHom (algebraMap R S))) ≫
          (EtaleTargetMaps.Components.affineMap R f).left := pullback.lift_fst _ _ _
    rw [hp, ← Category.assoc, affineBaseChangeIso_inv_fst, affineBaseChangeIso_inv_fst]
    change Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom) ≫
        Spec.map (CommRingCat.ofHom f.toRingHom) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id S S) f).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : C →ₐ[R] S ⊗[R] C).toRingHom)
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  · exact Over.w _ |>.trans (Over.w _).symm

variable {R} [HenselianLocalRing R]

/-- Every native special-fiber map into the finite etale affine target
has a unique integral lift. No special-fiber identification is an input. -/
theorem affine_special_fiber_hom_bijective
    [Module.Finite R A] [Module.Finite R C] [Algebra.Etale R C] :
    Function.Bijective
      ((Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).map
        (X := EtaleTargetMaps.Components.affineOver R A) (Y := EtaleTargetMaps.Components.affineOver R C)) := by
  let k := IsLocalRing.ResidueField R
  let F := Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
  let eA : F.obj (EtaleTargetMaps.Components.affineOver R A) ≅ EtaleTargetMaps.Components.affineOver k (k ⊗[R] A) := affineBaseChangeIso R k A
  let eC : F.obj (EtaleTargetMaps.Components.affineOver R C) ≅ EtaleTargetMaps.Components.affineOver k (k ⊗[R] C) := affineBaseChangeIso R k C
  constructor
  · intro f g h
    let a : C →ₐ[R] A := ((algSpec.fullyFaithful (R := .of R)).preimage f).unop.hom
    let b : C →ₐ[R] A := ((algSpec.fullyFaithful (R := .of R)).preimage g).unop.hom
    have ha : EtaleTargetMaps.Components.affineMap R a = f := (algSpec.fullyFaithful (R := .of R)).map_preimage f
    have hb : EtaleTargetMaps.Components.affineMap R b = g := (algSpec.fullyFaithful (R := .of R)).map_preimage g
    have hab : a = b := EtaleTargetMaps.Components.affine_specialization_injective R A a b (by rwa [ha, hb])
    exact ha.symm.trans ((congrArg (EtaleTargetMaps.Components.affineMap R) hab).trans hb)
  · intro φ
    let φa : k ⊗[R] C →ₐ[k] k ⊗[R] A :=
      ((algSpec.fullyFaithful (R := .of k)).preimage (eA.inv ≫ φ ≫ eC.hom)).unop.hom
    have hφ : EtaleTargetMaps.Components.affineMap k φa = eA.inv ≫ φ ≫ eC.hom :=
      (algSpec.fullyFaithful (R := .of k)).map_preimage _
    obtain ⟨f, hf⟩ := (OAI.Algebra.LocalRing.HenselianLifting.Construction.finiteEtale_baseChange_hom_bijective R C A).2 φa
    change Algebra.TensorProduct.map (AlgHom.id k k) f = φa at hf
    refine ⟨EtaleTargetMaps.Components.affineMap R f, ?_⟩
    apply (cancel_epi eA.inv).mp
    change eA.inv ≫ F.map (EtaleTargetMaps.Components.affineMap R f) = eA.inv ≫ φ
    have hn : eA.inv ≫ F.map (EtaleTargetMaps.Components.affineMap R f) =
        EtaleTargetMaps.Components.affineMap k (Algebra.TensorProduct.map (AlgHom.id k k) f) ≫ eC.inv :=
      affineBaseChangeIso_naturality R k f
    have hc : EtaleTargetMaps.Components.affineMap k (Algebra.TensorProduct.map (AlgHom.id k k) f) =
        eA.inv ≫ φ ≫ eC.hom := (congrArg (EtaleTargetMaps.Components.affineMap k) hf).trans hφ
    exact hn.trans ((congrArg (fun g => g ≫ eC.inv) hc).trans (by
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.AffineSpecialFiber.Components
