import OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers
import Mathlib.Topology.Sheaves.Sheaf

/-! # Line Bundle Power Map -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.LineBundlePowerMap

noncomputable section

/-!
# Homomorphisms: the canonical Frobenius map of a line bundle

The diagonal of a p-multilinear map out of a line bundle is additive in
characteristic p. Additivity is checked on actual local frames and glued
using separatedness of the target sheaf.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

theorem sections_cyclic_of_frame {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (L : Y.Modules) (e : L.restrict f ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (U : X.Opens) :
    ∃ s : Γ(L, f ''ᵁ U), ∀ t : Γ(L, f ''ᵁ U), ∃ r : Γ(Y, f ''ᵁ U), r • s = t := by
  let a := L.restrictAppIso f U
  let s := a.hom (e.inv.app U (1 : Γ(X, U)))
  refine ⟨s, fun t => ?_⟩
  let c : Γ(X, U) := e.hom.app U (a.inv t)
  refine ⟨(f.appIso U).inv c, ?_⟩
  calc
    (f.appIso U).inv c • s = a.hom (c • e.inv.app U (1 : Γ(X, U))) := rfl
    _ = a.hom (e.inv.app U (c • (1 : Γ(X, U)))) := by
      exact congrArg a.hom (e.inv.app_smul c (1 : Γ(X, U))).symm
    _ = a.hom (e.inv.app U c) := by rw [smul_eq_mul, mul_one]
    _ = t := by
      change a.hom ((e.hom ≫ e.inv).app U (a.inv t)) = t
      rw [e.hom_inv_id]
      exact ConcreteCategory.congr_hom a.inv_hom_id t

theorem lineBundle_sections_locally_cyclic {X : Scheme.{u}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (U : X.Opens) (x : X) (hx : x ∈ U) :
    ∃ V : X.Opens, ∃ _hVU : V ≤ U, x ∈ V ∧
      ∃ s : Γ(L.sheaf, V), ∀ t : Γ(L.sheaf, V), ∃ r : Γ(X, V), r • s = t := by
  obtain ⟨W, hxW, ⟨e⟩⟩ := L.locallyTrivial x
  let V := U ⊓ W
  let eV : (Scheme.Modules.pullback V.ι).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule V.toScheme :=
    (Scheme.Modules.pullbackCongr (X.homOfLE_ι (show V ≤ W from inf_le_right)).symm).app
        L.sheaf ≪≫
      (Scheme.Modules.pullbackComp (X.homOfLE (show V ≤ W from inf_le_right)) W.ι).symm.app
        L.sheaf ≪≫
      (Scheme.Modules.pullback (X.homOfLE (show V ≤ W from inf_le_right))).mapIso e ≪≫
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (X.homOfLE (show V ≤ W from inf_le_right))
  refine ⟨V, inf_le_left, ⟨hx, hxW⟩, ?_⟩
  have h := sections_cyclic_of_frame V.ι L.sheaf
    (((Scheme.Modules.restrictFunctorIsoPullback V.ι).app L.sheaf) ≪≫ eV) ⊤
  erw [Scheme.Opens.ι_image_top] at h
  exact h

theorem multilinear_diagonal_smul {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (n : ℕ) (β : MultilinearMap R (fun _ : Fin n => M) N) (r : R) (x : M) :
    β (fun _ => r • x) = r ^ n • β (fun _ => x) := by
  simpa using β.map_smul_univ (fun _ => r) (fun _ => x)

/-- A multilinear map out of a line bundle is determined by its diagonal.
This holds in every characteristic, by the local rank-one property. -/
theorem lineBundle_multilinear_ext_diagonal {X : Scheme.{u}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (n : ℕ) {P : X.Modules} (β γ : AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap L.sheaf n P)
    (h : ∀ (U : X.Opens) (s : Γ(L.sheaf, U)),
      β.app U (fun _ => s) = γ.app U (fun _ => s)) : β = γ := by
  apply AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap.ext
  intro U
  apply MultilinearMap.ext
  intro s
  apply P.isSheaf.section_ext
  intro x hx
  obtain ⟨V, hVU, hxV, v, hv⟩ := lineBundle_sections_locally_cyclic L U x hx
  refine ⟨V, hVU, hxV, ?_⟩
  rw [β.naturality, γ.naturality]
  choose a ha using fun i => hv (L.sheaf.presheaf.map (homOfLE hVU).op (s i))
  have hs : (fun i => L.sheaf.presheaf.map (homOfLE hVU).op (s i)) = fun i => a i • v :=
    funext (fun i => (ha i).symm)
  rw [hs, (β.app V).map_smul_univ a (fun _ => v), (γ.app V).map_smul_univ a (fun _ => v), h]

theorem lineBundle_diagonal_add {X : Scheme.{u}}
    (p : ℕ) (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (P : X.Modules) (β : AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap L.sheaf p P)
    (U : X.Opens) (s t : Γ(L.sheaf, U)) :
    β.app U (fun _ => s + t) = β.app U (fun _ => s) + β.app U (fun _ => t) := by
  apply P.isSheaf.section_ext
  intro x hx
  obtain ⟨V, hVU, hxV, v, hv⟩ := lineBundle_sections_locally_cyclic L U x hx
  refine ⟨V, hVU, hxV, ?_⟩
  rw [map_add, β.naturality, β.naturality, β.naturality]
  simp only [map_add]
  obtain ⟨a, ha⟩ := hv (L.sheaf.presheaf.map (homOfLE hVU).op s)
  obtain ⟨b, hb⟩ := hv (L.sheaf.presheaf.map (homOfLE hVU).op t)
  simp only [← ha, ← hb, ← add_smul]
  rw [multilinear_diagonal_smul, multilinear_diagonal_smul, multilinear_diagonal_smul]
  rw [← add_smul]
  exact congrArg (fun r : Γ(X, V) => r • β.app V (fun _ => v))
    ((Frobenius.Construction.powerRingHom p hp Γ(X, V) (Frobenius.Construction.section_prime_eq_zero p X hX V)).map_add a b)

/-- The diagonal is Frobenius-semilinear, as a map to the direct image
of the target sheaf under the actual absolute Frobenius. -/
def lineBundleFrobeniusToPushforward {X : Scheme.{u}}
    (p : ℕ) (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (P : X.Modules) (β : AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap L.sheaf p P) :
    L.sheaf ⟶ (Scheme.Modules.pushforward (Frobenius.Construction.absoluteFrobenius p hp X hX)).obj P where
  val.app U := by
    let Q : ModuleCat (X.ringCatSheaf.obj.obj U) :=
      ((Scheme.Modules.pushforward (Frobenius.Construction.absoluteFrobenius p hp X hX)).obj P).val.obj U
    let : Module (X.ringCatSheaf.obj.obj U) Q := Q.isModule
    exact (ModuleCat.ofHom (Y := Q) {
      toFun s := (show Q from β.app U.unop (fun _ => s))
      map_add' := lineBundle_diagonal_add p hp hX L P β U.unop
      map_smul' r s := multilinear_diagonal_smul p (β.app U.unop) r s } :
      L.sheaf.val.obj U ⟶ Q)
  val.naturality {U V} h := by
    ext s
    exact (β.naturality h.unop (fun _ => s)).symm

theorem lineBundleFrobeniusToPushforward_injective {X : Scheme.{u}}
    (p : ℕ) (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (P : X.Modules) :
    Function.Injective (lineBundleFrobeniusToPushforward p hp hX L P) := by
  intro β γ h
  apply lineBundle_multilinear_ext_diagonal L p β γ
  intro U s
  exact ConcreteCategory.congr_hom (congrArg (fun f => f.app U) h) s

theorem lineBundleFrobeniusToPushforward_postcomp {X : Scheme.{u}}
    (p : ℕ) (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) {P Q : X.Modules} (β : AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap L.sheaf p P) (f : P ⟶ Q) :
    lineBundleFrobeniusToPushforward p hp hX L Q (β.postcomp f) =
      lineBundleFrobeniusToPushforward p hp hX L P β ≫
        (Scheme.Modules.pushforward (Frobenius.Construction.absoluteFrobenius p hp X hX)).map f := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  rfl

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.LineBundlePowerMap
