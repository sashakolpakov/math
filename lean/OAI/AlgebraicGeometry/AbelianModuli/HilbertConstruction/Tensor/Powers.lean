import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles
import Mathlib.LinearAlgebra.Multilinear.Basic

/-! # Powers -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers

noncomputable section

/-!
The universal property of tensor powers of module sheaves, expressed in
terms of actual multilinear maps on sections. This provides a concrete
predicate for powers of a line bundle, without an opaque tensor-power API.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

/-- Multilinear maps of sheaves, compatible with every restriction map. -/
structure SheafMultilinearMap (L : X.Modules) (n : ℕ) (M : X.Modules) where
  app (U : X.Opens) : MultilinearMap Γ(X, U) (fun _ : Fin n => Γ(L, U)) Γ(M, U)
  naturality {U V : X.Opens} (h : V ⟶ U) (s : Fin n → Γ(L, U)) :
    M.presheaf.map h.op (app U s) =
      app V (fun i => L.presheaf.map h.op (s i))

namespace SheafMultilinearMap

variable {L M N P : X.Modules} {n : ℕ}

@[ext]
theorem ext {β γ : SheafMultilinearMap L n M} (h : ∀ U, β.app U = γ.app U) : β = γ := by
  cases β
  cases γ
  congr
  exact funext h

/-- The linear map on sections induced by a module-sheaf morphism. -/
def homApp (f : M ⟶ N) (U : X.Opens) : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) where
  toFun s := f.app U s
  map_add' s t := (f.app U).hom.map_add s t
  map_smul' r s := f.app_smul r s

/-- Postcomposition of a multilinear map by a sheaf morphism. -/
def postcomp (β : SheafMultilinearMap L n M) (f : M ⟶ N) :
    SheafMultilinearMap L n N where
  app U := (homApp f U).compMultilinearMap (β.app U)
  naturality {U V} h s := by
    change N.presheaf.map h.op (f.app U (β.app U s)) =
      f.app V (β.app V (fun i => L.presheaf.map h.op (s i)))
    have hf := ConcreteCategory.congr_hom (f.mapPresheaf.naturality h.op) (β.app U s)
    exact hf.symm.trans (congrArg (fun t => f.app V t) (β.naturality h s))

@[simp]
theorem postcomp_id (β : SheafMultilinearMap L n M) : β.postcomp (𝟙 M) = β := by
  ext U s
  rfl

theorem postcomp_comp (β : SheafMultilinearMap L n M) (f : M ⟶ N) (g : N ⟶ P) :
    β.postcomp (f ≫ g) = (β.postcomp f).postcomp g := by
  ext U s
  rfl

/-- The tautological unary multilinear map. -/
def unary (L : X.Modules) : SheafMultilinearMap L 1 L where
  app U := (MultilinearMap.ofSubsingleton Γ(X, U) Γ(L, U) Γ(L, U) (0 : Fin 1))
    LinearMap.id
  naturality _ _ := rfl

/-- A unary multilinear map is an ordinary morphism of module sheaves. -/
def unaryToHom (β : SheafMultilinearMap L 1 M) : L ⟶ M where
  val.app U := ModuleCat.ofHom
    ((MultilinearMap.ofSubsingleton Γ(X, U.unop) Γ(L, U.unop) Γ(M, U.unop)
      (0 : Fin 1)).symm (β.app U.unop))
  val.naturality {U V} h := by
    ext s
    exact (β.naturality h.unop (fun _ => s)).symm

@[simp]
theorem unary_postcomp_unaryToHom (β : SheafMultilinearMap L 1 M) :
    (unary L).postcomp β.unaryToHom = β := by
  ext U s
  change β.app U (fun _ => s 0) = β.app U s
  congr 1
  funext i
  congr 1
  exact Subsingleton.elim _ _

@[simp]
theorem unaryToHom_unary_postcomp (f : L ⟶ M) :
    ((unary L).postcomp f).unaryToHom = f := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  rfl

end SheafMultilinearMap

/-- `P` is an `n`th tensor power of `L` when morphisms out of `P` correspond
bijectively to `n`-multilinear maps out of `L`, by postcomposition. -/
def IsTensorPower (L : X.Modules) (n : ℕ) (P : X.Modules) : Prop :=
  ∃ β : SheafMultilinearMap L n P,
    ∀ Q : X.Modules, Function.Bijective (fun f : P ⟶ Q => β.postcomp f)

theorem isTensorPower_one (L : X.Modules) : IsTensorPower L 1 L := by
  refine ⟨SheafMultilinearMap.unary L, fun Q => ?_⟩
  exact ⟨fun f g h => by
      simpa using congrArg SheafMultilinearMap.unaryToHom h,
    fun β => ⟨β.unaryToHom, β.unary_postcomp_unaryToHom⟩⟩

/-- The universal property determines the tensor power up to isomorphism. -/
theorem IsTensorPower.unique {L P Q : X.Modules} {n : ℕ}
    (hP : IsTensorPower L n P) (hQ : IsTensorPower L n Q) : Nonempty (P ≅ Q) := by
  obtain ⟨β, hβ⟩ := hP
  obtain ⟨γ, hγ⟩ := hQ
  obtain ⟨f, hf⟩ := (hβ Q).surjective γ
  obtain ⟨g, hg⟩ := (hγ P).surjective β
  refine ⟨⟨f, g, ?_, ?_⟩⟩
  · apply (hβ P).injective
    exact (β.postcomp_comp f g).trans
      ((congrArg (fun δ : SheafMultilinearMap L n Q => δ.postcomp g) hf).trans
        (hg.trans β.postcomp_id.symm))
  · apply (hγ Q).injective
    exact (γ.postcomp_comp g f).trans
      ((congrArg (fun δ : SheafMultilinearMap L n P => δ.postcomp f) hg).trans
        (hf.trans γ.postcomp_id.symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers
