

Ltac splits :=
  match goal with 
  | |- _ /\ _ => split;splits
  | |- _ => idtac end.

Ltac Destruct H :=
  match type of H with
  | exists (_ : ?A), _ =>  
              match A with 
              | _ => destruct H as [? H];Destruct H
              end
  | _ /\ _ => let H0 := fresh "H" in 
              destruct H as [H H0];
              Destruct H;
              Destruct H0
  | _ \/ _ => destruct H as [H | H];
              Destruct H
  | _ => (discriminate || contradiction  || idtac)
  end.
