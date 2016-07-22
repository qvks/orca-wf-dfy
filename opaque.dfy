/* 
 * Var naming convention: 
 * a: ActorAddr
 * i: Addr 
 * c: Config 
 * st: State
 */
abstract module Opaque{
    ////CONFIG////
    type Config
    type Actor 
    type Frame
    datatype Msg = orca(i: Addr, z: int) | app(f: Frame) | ERR 
    function Heap(c: Config, i: Addr, fid: FId) : Addr 
    function allocated_addresses(c: Config) : set<Addr>
    
    ////IDs////
    type FId 
    type BId  
    type ClassId
    type VarId

    ////ADDRESSES////
    datatype Addr = OA(ObjectAddr) | AA(ActorAddr) | Null
    type ObjectAddr 
    type ActorAddr
    
    ////PATHS////
    datatype Capability = WRITE | READ | TAG | ERR
    type DP 
    type SP
    
    datatype Optional<T> = Some(o: T) | None 
    
    ////ACTORS////
    //lemma all valid actor addresses are in the domain of Actors
    function Actors(c: Config, a: ActorAddr) : Actor

    //Queues//
    function queue_length(c: Config, a: ActorAddr) : nat 
    function queue_n(c: Config, a: ActorAddr, n: nat) : Msg 

    function prev_message(c: Config, a: ActorAddr, n: nat) : Msg
    {
        if n >= 1 then queue_n(c, a, n-1) else Msg.ERR
    }

    predicate WF_queue(c: Config, a: ActorAddr) {
        (forall n: nat :: n < queue_length(c,a) ==> queue_n(c, a, n) != Msg.ERR) &&
        (forall n: nat :: n >= queue_length(c,a) ==> queue_n(c,a,n) == Msg.ERR)
    }

    predicate push(c: Config, a: ActorAddr, msg: Msg, c': Config)
    {
        WF_queue(c, a) && 
        msg != Msg.ERR &&
        queue_length(c', a) == queue_length(c, a) + 1 && 
        queue_n(c', a, queue_length(c,a)) == msg &&
        (forall n: nat :: n != queue_length(c,a) ==> 
        queue_n(c', a, n) == queue_n(c, a, n))
    }

    lemma {:verify false} push_preserves_WF_queue(c: Config, a: ActorAddr, msg: Msg, c': Config) 
        requires push(c, a, msg, c')
        ensures WF_queue(c', a)
    {
    }
    
    predicate pop(c:Config, a:ActorAddr, c': Config)  
    {
        WF_queue(c, a) &&
        queue_length(c', a) == queue_length(c, a) - 1 &&
        forall n: nat :: n >= 0 ==>
        queue_n(c', a, n) == queue_n(c, a, n+1) 
    }

    lemma {:verify false} pop_preserves_WF_queue(c: Config, a: ActorAddr, c': Config) 
        requires pop(c, a, c')
        ensures WF_queue(c', a)
    {
    }
    
    ////REFERENCE COUNTS////
    function RC(c: Config, i: Addr, a: ActorAddr) : nat
    function OMC(c: Config, i: Addr) : int
    function LRC(c: Config, i: Addr) : int
    function FRC(c: Config, i: Addr) : int
    function AMC(c: Config, i: Addr) : int 
    //{|(set x | exists a,k :: 0<=k<queue_length(c, a) && x==(a,k) && Reach(c,a,k,i))|}

    predicate A(c: Config, a: ActorAddr, dp: DP, i: Addr, k: Capability)

    ////DATA RACE FREEDOM////
    predicate DFR(c: Config) {
        forall a, a': ActorAddr, p, p': DP, i: Addr, k: Capability:: 
            a != a' && 
            A(c, a, p, i, WRITE) &&
            A(c, a', p', i, k) ==> 
            k == TAG
    }
    
    ////INVARIANTS////
    predicate INV_2(c: Config) {
        forall i, dp, mp, k, a, a_own :: 
            (A(c, a, dp, i, k) && 
            !Owner(c, i, a)) ||
            (A(c, a_own, mp, i, k) &&
            Owner(c, i, a_own) &&
            is_a_message_path(c, mp)) ==>
            LRC(c, i) > 0
                             
    }
    predicate is_a_message_path(c: Config, mp: DP) 
 
    predicate INV_3(c: Config) {
        forall i, dp, k, a :: 
            A(c, a, dp, i, k) &&
            !Owner(c, i, a) ==> 
            RC(c, i, a) > 0
    }




    ///////////////PSEUDO CODE FOR RECEIVING MESSAGES (FIGURE 6)///////////////

    ////RcvApp////
    predicate RcvApp(c: Config, a: ActorAddr, c': Config) 
        requires actor_state_idle(c, a)  
        requires queue_head_app(c, a)
    {
        actor_state_rcv(c', a) &&
        //0 here, 1 in the paper, leave which one?
        actor_ws(c', a) == set i | 
            i in allocated_addresses(c) &&
            exists mp,k ::
            mp in paths_from_message_n(c, a, 0) &&
            A(c,a,mp,i,k)
    }
    
    
    predicate RcvToExe(c: Config, a: ActorAddr, c': Config)
    {
        actor_state_rcv(c, a) &&
        queue_head_app(c, a) &&
        actor_state_exe(c', a) && 
        actor_state_exe_frame(c', a) == frame_from_app_message_n(c,a,0) &&
        pop(c, a, c') &&
        (forall i :: i in actor_ws(c,a) && Owner(c, i, a) ==> RC(c', i, a) == RC(c, i, a) - 1) &&
        (forall i :: i in actor_ws(c,a) && !Owner(c, i, a) ==> RC(c', i, a) == RC(c, i, a) + 1) &&
        (forall i :: i !in actor_ws(c,a) ==> RC(c', i, a) == RC(c, i, a)) &&
        //TODO: TAKE THIS OUT INTO OWNERSHIP_PRESERVED(C)
        (forall i, a' :: Owner(c,i,a') == Owner(c',i,a')) &&
        (forall i, a' :: a' != a ==> RC(c', i, a') == RC(c, i, a'))
    } 

    lemma {:verify false} RcvToExe_Increases_A(c: Config, a: ActorAddr, c': Config)
        requires RcvToExe(c, a, c')
        ensures forall lp, i, k :: A(c, a, lp, i, k) ==> A(c', a, lp, i, k)
        ensures forall lp, i, k :: A(c', a, lp, i, k) ==> A(c, a, lp, i, k) || i in actor_ws(c, a)
        ensures forall lp, i, k, a' :: a' != a ==> A(c', a', lp, i, k) == A(c, a', lp, i, k)
    

    lemma {:verify false} RcvToExe_preserves_INV_3(c: Config, a': ActorAddr, c': Config) 
        requires INV_3(c) 
        requires RcvToExe(c, a', c')
        ensures INV_3(c')
    {
        RcvToExe_Increases_A(c, a', c');
        forall i, lp, k, a | A(c', a, lp, i, k) &&
                          !Owner(c', i ,a) 
            ensures RC(c', i, a) > 0     
        {
            if a' == a && i in actor_ws(c, a) {
                assert RC(c, i, a) >= 0;
                assert RC(c', i, a) == RC(c, i, a) + 1;
            } else {
                assert RC(c', i, a) == RC(c, i, a);
                assert RC(c, i, a) > 0;
                assert RC(c', i, a) > 0;
            }
        }
    }
    
    ////AUXILIARY FOR RcvApp////
    predicate actor_state_idle(c: Config, a: ActorAddr)

    predicate queue_head_app(c: Config, a: ActorAddr)
        ensures queue_length(c, a) > 0

    predicate actor_state_rcv(c: Config, a: ActorAddr)

    function paths_from_message_n(c: Config, a: ActorAddr, n: nat) : set<DP>
        requires n < queue_length(c, a) 

    function actor_ws(c: Config, a: ActorAddr) : set<Addr>
        requires actor_state_rcv(c, a)

    function queue_head_iotas(c: Config, a: ActorAddr) : set<Addr>
        requires queue_head_app(c, a)
    
    predicate Owner(c: Config, i: Addr, a: ActorAddr)

    predicate actor_state_exe(c: Config, a: ActorAddr)

    function actor_state_exe_frame(c: Config, a: ActorAddr) : Frame 

    function frame_from_app_message_n(c: Config, a: ActorAddr, n: nat) : Frame

    ///////////////PSEUDO CODE FOR RECEIVING AN ORCA MESSAGE (FIGURE 7)///////////////

    predicate INV_6(c: Config) {
        forall n: nat, i, a ::
        ((Owner(c, i, a) && 
        queue_at_n_orca(c, a, n) &&
        queue_at_n_orca_i(c, a, n) == i) ==>
        (LRC(c, i) > 0 &&
        forall m: nat :: m < queue_length(c, a) ==> 
        LRC(c, i) + sum_over_queue_i(c, a, i, m) >= 0))
        
    }

    ////AUXILIARY FOR INV_6////
    predicate queue_at_n_orca(c: Config, a: ActorAddr, n: nat)
    function queue_at_n_orca_i(c: Config, a: ActorAddr, n: nat) : Addr
    function queue_at_n_orca_z(c: Config, a: ActorAddr, n: nat) : int 

    function sum_over_queue_i(c: Config, a: ActorAddr, i: Addr, n: nat) : int 
        requires n <= queue_length(c, a)
    
    ////rcvORCA////
    predicate rcvORCA(c: Config, a: ActorAddr, c': Config) 
    {   
        var i := queue_at_n_orca_i(c, a, 0);
        var z := queue_at_n_orca_z(c, a, 0);

        LRC(c, queue_at_n_orca_i(c, a, 0)) > 0 &&
        Owner(c, queue_at_n_orca_i(c, a, 0), a) &&
        queue_at_n_orca(c, a, 0) &&
        actor_state_idle(c, a) &&

        pop(c, a, c') &&
        RC(c', i, a) == RC(c, i, a) + z &&
        LRC(c', i) == LRC(c, i) + z 
    }
    
    lemma rcvORCA_preserves_INV_6(c: Config, a: ActorAddr, c': Config)
        requires INV_6(c)
        requires rcvORCA(c, a, c')
        ensures INV_6(c')
    {
       // forall n: nat, i, a | 
    }
    
    /*
    lemma rcvORCA_preserves_INV_2(c: Config, a: ActorAddr, c': Config) 
        requires INV_2(c)
        requires rcvORCA(c, a, c')
        ensures INV_2(c')
    {
        
    } */   

    predicate queue_head_orca(c: Config, a: ActorAddr)
    function queue_head_i(c: Config, a: ActorAddr) : Addr
    function queue_head_orca_z(c: Config, a: ActorAddr) : int 

    
  
//    lemma rcvORCA_changes_RC(c: Config, a: ActorAddr, c': Config)
//        requires rcvORCA(c, a, c') 
    
        
} 

/* IGNORE
    //States// 
    datatype State = idl | exe(f: Frame) | snd(f': Frame, a: Actor, m: Msg, ws: Workset)
                | mkU(ms: Marks) | trc(ms': Marks) | mkR(ms'': Marks) | cll(ms''': Marks)
    type Marks 
    type Workset = set<Addr> //opaque - how?
    datatype RU = R | U
    function Marks_to_RU(m: Marks) : RU



    ////MESSAGES////
    datatype Msg = orca(i: Addr, z: int) | app(f: Frame) | ERR 
    //datatype Frame = CFrame(b: BId, Map: map<VarId, Addr>) //opaque - how? 
    datatype Frame = Frame(b: BId) 
    function var_to_addr(f: Frame, v: VarId) : Addr
    
    
    ////IDs////
    type FId 
    type BId  
    type ClassId
    type VarId

    ////PATHS//// 
    datatype DP = This | LP(zero: int, x: VarId) | MP(k: int, x': VarId) | cons(dp: DP, f: FId)
    datatype SP = This | bsp(b: BId, x: VarId) | cons(sp: SP, f: FId)
    datatype Capability = WRITE | READ | TAG | ERR
    


    ////REFERENCE COUNTS////
    function RC(c: Config, i: Addr, a: ActorAddr) : int 
    function OMC(c: Config, i: Addr) : int
    function LRC(c: Config, i: Addr) : int
    function FRC(c: Config, i: Addr) : int
    function AMC(c: Config, i: Addr) : int 
    //{|(set x | exists a,k :: 0<=k<queue_length(c, a) && x==(a,k) && Reach(c,a,k,i))|}
    
    function Owner(c: Config, i: Addr) : ActorAddr
    function Field(c: Config, i: Addr, f: FId) : Addr //what do we need this for?
    function Class(c: Config, a: ActorAddr) : ClassId 
    function Addrs(c: Config) : set<ActorAddr>
    
    predicate Reach(c: Config, a: ActorAddr, n: nat, i: Addr)

    ////DATA-RACE FREEDOM//// 
    function sees(cid: ClassId, sp: SP) : Capability
    function views(c: Config, a: ActorAddr, p:DP) : Capability
    
    lemma {:verify true} A1(a: Actor, sp: SP, f: FId, cappa: Capability) 
    requires sees(a.cl, SP.cons(sp, f)) == cappa //pass cappa as param instead?
    ensures exists cappa' :: cappa' != TAG && sees(a.cl, sp) == cappa' 


    lemma {:verify true} A2(a: Actor, sp: SP, f: FId) 
    requires sees(a.cl, SP.cons(sp, f)) == WRITE
    ensures sees(a.cl, sp) == WRITE

    function C(c: Config, a: ActorAddr, dp: DP) : Addr 
    function A(c: Config, a: ActorAddr, dp: DP) : (Addr, Capability)
   /*
     predicate WF_A(c: Config, a: ActorAddr, dp: DP) {
        forall i: Addr :: ((exists k: Capability :: 
        A(c,a,dp) == (i, k)) <==> (C(c,a,dp) == i && views(c,a,dp) == k 
                                || k == TAG && exists k', i', p' ::
                                (p == Cons(p',) && A(c,a,p') == (i', k') && Owner(c, i') == i)))
                                                                      
    }
    */
    /*
    predicate DFR(c: Config) {
        forall a, a': ActorAddr, p, p': DP, i: Addr :: (a != a' && (exists k :: A(c, a, p) == (i, k) && k==WRITE) 
                                            ==> (exists k' :: A(c, a', p') == (i, k') ==> k' == TAG))
    } */
    predicate DFR(c: Config) {
        forall a, a': ActorAddr, p, p': DP, i: Addr :: (a != a' && (exists k :: A(c, a, p) == (i, k) && k==WRITE) 
                                            && exists k' :: A(c, a', p') == (i, k') ==> k' == TAG)
    }

    ////AUXILIARY FUNCTION////
    //TODO: separate into its own module
    function queue_length(c: Config, a: ActorAddr) : int {
        Actors(a,c).q.length
    
    }
} 
