import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SectionsExcision
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechZero
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechFunctor

/-! # Ordered Cech Edge -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCechEdge

noncomputable section

/-! The canonical supported-section augmentation into the actual
augmented ordered Čech total of a sheaf complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem compose_inverse_square {D : Type*} [Category* D]
    {N₁ N₂ C₁ C₂ T₁ T₂ : D}
    (s : N₁ ⟶ N₂) (a : N₁ ⟶ C₁) (b : N₂ ⟶ C₂) (d : C₁ ⟶ C₂)
    (e₁ : T₁ ≅ C₁) (e₂ : T₂ ≅ C₂) (m : T₁ ⟶ T₂)
    (h₁ : s ≫ b = a ≫ d) (h₂ : m ≫ e₂.hom = e₁.hom ≫ d) :
    s ≫ b ≫ e₂.inv = a ≫ e₁.inv ≫ m := by
  apply (cancel_mono e₂.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h₂, ← Category.assoc e₁.inv e₁.hom d, e₁.inv_hom_id, Category.id_comp]
  exact h₁

universe u v w z
variable (R : Type u) [CommRing R] (X : TopCat.{v})
  {C : Type w} [Preorder C] [HasFiniteProducts C]
  (F : C ⥤ Opens X) {ι : Type w} [LinearOrder ι] (U : ι → C) (O : Opens X)

local notation "V" => F.obj (⊤_ C)

local instance coefficient_limits [UnivLE.{w, z}] : HasLimitsOfSize.{w, w} (ModuleCat.{z} R) :=
  ModuleCat.hasLimitsOfSize.{w, w, z, u}

local instance coefficient_colimits : HasColimitsOfSize.{0, 0} (ModuleCat.{z} R) :=
  ModuleCat.hasColimitsOfSize.{z, u, 0, 0} R

def supportFunctor :
    Sheaf (Opens.grothendieckTopology X) (ModuleCat.{max u v w z} R) ⥤
      ModuleCat.{max u v w z} R :=
  SectionsExcision.supported V (V ⊓ O) inf_le_left

instance supportFunctor_additive : (supportFunctor.{u,v,w,z} R X F O).Additive := by
  dsimp only [supportFunctor]
  infer_instance

def presheaves : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{max u v w z} R) ⥤ Cᵒᵖ ⥤ ModuleCat.{max u v w z} R :=
  sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{max u v w z} R) ⋙
    (Functor.whiskeringLeft Cᵒᵖ (Opens X)ᵒᵖ (ModuleCat.{max u v w z} R)).obj F.op

instance presheaves_additive : (presheaves.{u,v,w,z} R X F).Additive := by
  dsimp only [presheaves]
  infer_instance

variable (K : CochainComplex (Sheaf (Opens.grothendieckTopology X)
  (ModuleCat.{max u v w z} R)) ℕ)

def source : CochainComplex (ModuleCat.{max u v w z} R) ℕ := ((supportFunctor.{u,v,w,z} R X F O).mapHomologicalComplex (.up ℕ)).obj K

def presheafComplex : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v w z} R) ℕ :=
  ((presheaves.{u,v,w,z} R X F).mapHomologicalComplex (.up ℕ)).obj K

def bicomplex : HomologicalComplex₂ (ModuleCat.{max u v w z} R) (.up ℕ) (.up ℕ) :=
  AugmentedOrdered.CechFunctor.bicomplex (D := ModuleCat.{max u v w z} R) U
    (presheafComplex.{u,v,w,z} R X F K)

def component (q : ℕ) : (source.{u,v,w,z} R X F O K).X q ⟶ ((OrderedCechEdge.bicomplex.{u,v,w,z} R X F U K).X q).X 0 :=
  (SectionsExcision.inclusion V (V ⊓ O) inf_le_left).app (K.X q) ≫
    (AugmentedOrdered.CechZero.zeroIso (D := ModuleCat.{max u v w z} R) U (F.op ⋙ (K.X q).obj)).inv

theorem comm (q q' : ℕ) :
    component.{u,v,w,z} R X F U O K q ≫ ((OrderedCechEdge.bicomplex.{u,v,w,z} R X F U K).d q q').f 0 =
      (source.{u,v,w,z} R X F O K).d q q' ≫ component.{u,v,w,z} R X F U O K q' := by
  let f : F.op ⋙ (K.X q).obj ⟶ F.op ⋙ (K.X q').obj :=
    Functor.whiskerLeft F.op (K.d q q').hom
  exact (compose_inverse_square (D := ModuleCat.{max u v w z} R)
    ((supportFunctor.{u,v,w,z} R X F O).map (K.d q q'))
    ((SectionsExcision.inclusion V (V ⊓ O) inf_le_left).app (K.X q))
    ((SectionsExcision.inclusion V (V ⊓ O) inf_le_left).app (K.X q'))
    ((SectionsExcision.sections V).map (K.d q q'))
    (AugmentedOrdered.CechZero.zeroIso (D := ModuleCat.{max u v w z} R) U (F.op ⋙ (K.X q).obj))
    (AugmentedOrdered.CechZero.zeroIso (D := ModuleCat.{max u v w z} R) U (F.op ⋙ (K.X q').obj))
    (AugmentedOrdered.CechFunctor.objectMap (D := ModuleCat.{max u v w z} R) U f 0)
    ((SectionsExcision.inclusion V (V ⊓ O) inf_le_left).naturality (K.d q q'))
    (AugmentedOrdered.CechZero.zeroIso_naturality (D := ModuleCat.{max u v w z} R)
      (Q := F.op ⋙ (K.X q').obj) U (F.op ⋙ (K.X q).obj) f)).symm

variable (hO : ∀ i, F.obj (U i) ≤ O)

include hO in
theorem cocycle (q : ℕ) :
    component.{u,v,w,z} R X F U O K q ≫ ((OrderedCechEdge.bicomplex.{u,v,w,z} R X F U K).X q).d 0 1 = 0 := by
  change component.{u,v,w,z} R X F U O K q ≫
    (AugmentedOrdered.Cech.complex U (F.op ⋙ (K.X q).obj)).d 0 1 = 0
  have hd : (AugmentedOrdered.Cech.complex U (F.op ⋙ (K.X q).obj)).d 0 1 =
      AugmentedOrdered.Cech.differential U (F.op ⋙ (K.X q).obj) 0 :=
    CochainComplex.of_d (AugmentedOrdered.Cech.object U (F.op ⋙ (K.X q).obj))
      (AugmentedOrdered.Cech.differential U (F.op ⋙ (K.X q).obj)) 0
  rw [hd]
  apply Pi.hom_ext
  intro a
  rw [zero_comp, Category.assoc]
  change ((SectionsExcision.inclusion V (V ⊓ O) inf_le_left).app (K.X q) ≫
    (AugmentedOrdered.CechZero.zeroIso (D := ModuleCat.{max u v w z} R) U (F.op ⋙ (K.X q).obj)).inv) ≫
      AugmentedOrdered.Cech.differential U (F.op ⋙ (K.X q).obj) 0 ≫
        Pi.π (fun b : AugmentedOrdered.Cech.Index ι 1 =>
          (F.op ⋙ (K.X q).obj).obj (op ((AugmentedOrdered.Cech.formal U 1).obj b))) a = 0
  rw [Category.assoc, AugmentedOrdered.CechZero.zeroIso_inv_differential_π]
  let T := (AugmentedOrdered.Cech.formal U 1).obj a
  have hT : F.obj T ≤ V ⊓ O :=
    le_inf (leOfHom (F.map (terminal.from T)))
      ((leOfHom (F.map (Pi.π (fun i : Fin 1 => U (a.val i)) 0))).trans (hO (a.val 0)))
  have he : F.map (terminal.from T) =
      (homOfLE hT : F.obj T ⟶ V ⊓ O) ≫ homOfLE inf_le_left := Subsingleton.elim _ _
  change kernel.ι ((SectionsExcision.restriction V (V ⊓ O) inf_le_left).app (K.X q)) ≫
    (K.X q).obj.map (F.map (terminal.from T)).op = 0
  rw [he, op_comp, Functor.map_comp, ← Category.assoc]
  exact (congrArg (fun a => a ≫ (K.X q).obj.map (homOfLE hT).op)
    (kernel.condition ((SectionsExcision.restriction V (V ⊓ O) inf_le_left).app
      (K.X q)))).trans zero_comp

local instance total_exists : (OrderedCechEdge.bicomplex.{u,v,w,z} R X F U K).HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts _

def map : source.{u,v,w,z} R X F O K ⟶ (OrderedCechEdge.bicomplex.{u,v,w,z} R X F U K).total (.up ℕ) :=
  (AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge (bicomplex.{u,v,w,z} R X F U K)) (source.{u,v,w,z} R X F O K)
    (component.{u,v,w,z} R X F U O K) (fun q q' _ => comm.{u,v,w,z} R X F U O K q q')
    (cocycle.{u,v,w,z} R X F U O K hO)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCechEdge
