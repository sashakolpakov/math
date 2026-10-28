import OAI.AlgebraicGeometry.FormalGeometry.Completion.FrobeniusFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.Quasicoherence

/-! # Frobenius Diagonal -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FrobeniusDiagonal.Construction

noncomputable section

/-! The diagonal tensor power of an actual line bundle is Frobenius-semilinear. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

/-- On a rank-one module the diagonal of a multilinear map is a scalar power. -/
theorem multilinear_diagonal_frame {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {n : ℕ} (β : MultilinearMap R (fun _ : Fin n => M) N)
    (e : M ≃ₗ[R] R) (m : M) :
    β (fun _ => m) = (e m) ^ n • β (fun _ => e.symm 1) := by
  have hm : m = e m • e.symm 1 := by
    rw [← e.symm.map_smul, smul_eq_mul, mul_one, e.symm_apply_apply]
  calc
    β (fun _ => m) = β (fun _ => e m • e.symm 1) := congrArg β (funext fun _ => hm)
    _ = (e m) ^ n • β (fun _ => e.symm 1) := by
      simpa using β.map_smul_univ (fun _ => e m) (fun _ => e.symm 1)

/-- Additivity of the diagonal in finite-field degree follows in every rank-one frame. -/
theorem multilinear_diagonal_add (k : Type u) [Field k] [Fintype k]
    {R M N : Type u} [CommRing R] (κ : k →+* R)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (β : MultilinearMap R (fun _ : Fin (Fintype.card k) => M) N)
    (e : M ≃ₗ[R] R) (s t : M) :
    β (fun _ => s + t) = β (fun _ => s) + β (fun _ => t) := by
  rw [multilinear_diagonal_frame β e, multilinear_diagonal_frame β e s,
    multilinear_diagonal_frame β e t, map_add]
  have h := (Frobenius.Construction.finiteFieldPowerRingHom k κ).map_add (e s) (e t)
  change (e s + e t) ^ Fintype.card k = (e s) ^ Fintype.card k +
    (e t) ^ Fintype.card k at h
  rw [h, add_smul]

/-- A local line-bundle frame supplies scalar coordinates on every smaller open. -/
def lineBundleFrameCoordinates {X : Scheme.{u}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    {U V : X.Opens} (h : V ≤ U)
    (e : (Scheme.Modules.pullback U.ι).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme) :
    Γ(L.sheaf, V) ≃ₗ[Γ(X, V)] Γ(X, V) :=
  ((SheafOfModules.evaluation (X.ringCatSheaf.over U)
    (op (Over.mk (homOfLE h)))).mapIso (L.overFrameIso U e)).toLinearEquiv

/-- The tensor diagonal is additive on actual sections, including opens without a frame. -/
theorem lineBundle_tensorDiagonal_add (k : Type u) [Field k] [Fintype k]
    {X : Scheme.{u}} (κ : k →+* Γ(X, ⊤)) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (U : X.Opens) (s t : Γ(L.sheaf, U)) :
    (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMultilinear L.sheaf (Fintype.card k)).app U (fun _ => s + t) =
      (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMultilinear L.sheaf (Fintype.card k)).app U (fun _ => s) +
      (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMultilinear L.sheaf (Fintype.card k)).app U (fun _ => t) := by
  let P := AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule L.sheaf (Fintype.card k)
  let β := AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMultilinear L.sheaf (Fintype.card k)
  apply TopCat.Presheaf.section_ext (⟨P.presheaf, P.isSheaf⟩ :
    TopCat.Sheaf AddCommGrpCat.{u} X) U
  intro x hx
  obtain ⟨V, hxV, ⟨e⟩⟩ := L.locallyTrivial x
  let W := U ⊓ V
  let i : W ⟶ U := homOfLE inf_le_left
  have he := multilinear_diagonal_add k (Frobenius.Construction.sectionBaseMap k X κ W) (β.app W)
    (lineBundleFrameCoordinates L inf_le_right e)
    (L.sheaf.presheaf.map i.op s) (L.sheaf.presheaf.map i.op t)
  have hr : P.presheaf.map i.op (β.app U (fun _ => s + t)) =
      P.presheaf.map i.op (β.app U (fun _ => s) + β.app U (fun _ => t)) := by
    rw [(P.presheaf.map i.op).hom.map_add]
    rw [β.naturality i, β.naturality i, β.naturality i]
    simpa only [map_add] using he
  simpa only [TopCat.Presheaf.germ_res_apply] using
    congrArg (P.presheaf.germ W x ⟨hx, hxV⟩) hr

/-- The diagonal tensor power, as a morphism into the actual Frobenius direct image. -/
def lineBundleFrobeniusDiagonal (k : Type u) [Field k] [Fintype k]
    {X : Scheme.{u}} (κ : k →+* Γ(X, ⊤)) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) :
    L.sheaf ⟶ (Scheme.Modules.pushforward (Frobenius.Construction.qPowerSchemeFrobenius k X κ)).obj
      (AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule L.sheaf (Fintype.card k)) where
  val.app U := by
    let Q := ((Scheme.Modules.pushforward (Frobenius.Construction.qPowerSchemeFrobenius k X κ)).obj
      (AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule L.sheaf (Fintype.card k))).val.obj U
    let : Module Γ(X, U.unop) Q := Q.isModule
    exact ModuleCat.ofHom (Y := Q) {
    toFun s := (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMultilinear L.sheaf (Fintype.card k)).app U.unop (fun _ => s)
    map_add' s t := lineBundle_tensorDiagonal_add k κ L U.unop s t
    map_smul' r s := by
      change Γ(X, U.unop) at r
      change (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMultilinear L.sheaf (Fintype.card k)).app U.unop
        (fun _ => r • s) = r ^ Fintype.card k •
          (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMultilinear L.sheaf (Fintype.card k)).app U.unop (fun _ => s)
      simpa using (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMultilinear L.sheaf (Fintype.card k)).app U.unop
        |>.map_smul_univ (fun _ => r) (fun _ => s) }
  val.naturality {U V} h := by
    ext s
    exact ((AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMultilinear L.sheaf (Fintype.card k)).naturality h.unop
      (fun _ => s)).symm

/-- The actual global comparison from Frobenius pullback to the tensor power. -/
def lineBundleFrobeniusComparison (k : Type u) [Field k] [Fintype k]
    {X : Scheme.{u}} (κ : k →+* Γ(X, ⊤)) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) :
    (Scheme.Modules.pullback (Frobenius.Construction.qPowerSchemeFrobenius k X κ)).obj L.sheaf ⟶
      AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule L.sheaf (Fintype.card k) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (Frobenius.Construction.qPowerSchemeFrobenius k X κ)).homEquiv
    _ _).symm (lineBundleFrobeniusDiagonal k κ L)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FrobeniusDiagonal.Construction
