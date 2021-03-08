(**
  Module for handling the different traces on different Steps
**)

module TVLoopStart  = Map.Make(String)  (*   tv -> loop    *)
module TVStep    = Map.Make(String)  (*   tv -> step   *)

exception TvStepError of string


class tvset k_b =
  object (self)
    val mutable parent = "***"
    val mutable parentStep = 0

    val mutable tvLoopStart = TVLoopStart.empty
    val mutable tvStep = TVStep.empty
    val mutable k = k_b ;
    val mutable lcm = 0 ; 
    (* List of tv in step k, where no loop is set  *)
    val mutable num_k = []; 

    method getParentTuple = 
      begin
        if parent <> "***"
        then (
        self#setParentStep (self#getStep parent);
        (parent, parentStep )
        )else
          ("***",0)
      end

    method setParent tv = 
          parent <- tv

    method setParentStep n =
           parentStep <- n

    method addParent tv = 
            begin
                self#setParent tv;
                self#setParentStep 0;
                self#addToTVStep tv 0;
            end

    method getTuple tv = 
      begin
        let step = self#getStep tv in
        let bound = self#getBound tv in
        (step, bound )
      end
  
      
    method printTvStep = 
            begin
                Printf.printf "TV Step \n";
                TVStep.iter (fun key value -> Printf.printf "%s -> %d |" key value) tvStep;
                print_newline ()
            end

    method printTvLoop = 
            begin
              Printf.printf "TV Loop Start \n";
              TVLoopStart.iter (fun key value -> Printf.printf "%s -> %d |" key value) tvLoopStart;
              print_newline ();
              Printf.printf "TV Loop Run \n";
              print_newline ()
            end

    method printTrueFalse s b =
            if b then Printf.printf "%s -> 1 |" s else Printf.printf "%s -> 0 |"s
    

    method print =
            begin
              Printf.printf "parent(%s,%d) lcm(%d)" parent parentStep lcm;
              self#printTvStep;
              self#printTvLoop
            end

    method addToTVStep tv step = 
              tvStep <- TVStep.add tv step tvStep;
    
    method addToTVLoopStart tv loop =
            tvLoopStart <- TVLoopStart.add tv loop tvLoopStart;


    method addToTVSet pv p_step loop  =
        begin
          let tv = pv^"_"^(string_of_int p_step) in
          self#addToTVStep tv 0;
          self#addToTVLoopStart tv loop;
        end
    
    (* setter *)
    method addStepsAll n = 
          tvStep  <- TVStep.mapi (fun k v ->  (v+n) ) tvStep;


    method setStep tv n =
          self#addToTVStep tv n

    method setLoop tv l =
        tvLoopStart <- TVLoopStart.add tv l tvLoopStart

    (* Getter *)
    method getStep tv =
    try
        TVStep.find tv tvStep
    with Not_found -> ( self#print ; raise (TvStepError ("Not found getStep("^tv^"), probably unbound ap in formula"  ) ) )


    method getBound tv=
      try
          TVLoopStart.find tv tvLoopStart
      with  Not_found -> 0


    method isOnLoop  tv =
        if (self#getBound tv == 0)
        then false
        else true

      
    method allOnLoop = 
        (** todo check **)
        assert((TVStep.cardinal tvStep > 0));
        if( (TVStep.cardinal tvStep) == (TVLoopStart.cardinal tvLoopStart) )
        then ( self#set_lcm ;true)
        else false        

    method lcm_calc a b = 
          let ma_ab = abs(a * b) in
          if (ma_ab == 0 )
          then 0
          else ma_ab / (self#gcd a b)

    method  gcd a b =
        if b == 0
        then a
        else (
          let moduab = a mod b in
          self#gcd b moduab 
        )
      
    method set_lcm  = 
        let start = 1 in
        lcm <- TVLoopStart.fold (fun tv loop start -> self#lcm_calc start loop) tvLoopStart start

    method get_lcm = 
        if( lcm == 0 )
        then 
        (
          if self#allOnLoop
          then (self#set_lcm ; lcm )
          else assert(false) 
        )
        else lcm
     
    method addToNumK tv  =
         num_k <- tv::num_k 

    method setBoundAndStep tv i =
          self#addToTVStep tv i; 
          self#addToTVLoopStart tv i;
        

        

    method getBoundOrStep_ tv i = 
          assert (i == k);
          let bound = self#getBound tv in
          if bound == 0 
          then  (
                    self#addToNumK tv;
                    i
          )
          else
            (
            bound
            )

    method getStepOrBound tv i =
    assert ( i <= k);
      if i < k (* do nothing *)
      then i
      else (
            assert(i==k);
            self#getBoundOrStep_ tv i 
            ) 

    method resetStepsToLoop =
        begin 
          num_k <- [];
            tvStep <- TVStep.mapi (fun tv i -> (self#getStepOrBound tv i) ) tvStep; 
            num_k
        end

  end;;



