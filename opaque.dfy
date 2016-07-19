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
    type FId 
    function Heap(c: Config, i: Addr, fid: FId) : Addr 
    function allocated_addresses(c: Config) : set<Addr>
    

    ////ADDRESSES////
    datatype Addr = OA(ObjectAddr) | AA(ActorAddr) | Null
    type ObjectAddr 
    type ActorAddr
    

    ////ACTORS////
//    datatype Actor = Actor(st: State, cl: ClassId)
    //lemma RANGE OF ACTORS IS FINITE
    //lemma all valid actor addresses are in the domain of Actors
    function Actors(c: Config, a: ActorAddr) : Actor

    //Queues//
    //length added to convince Dafny that queues are finite 
    //Is there a better way?
    //datatype Queue = Queue(msg: Msg, length: int) //opaque - how?
    function queue_length(c: Config, a: ActorAddr) : nat 
    function queue_n(c: Config, a: ActorAddr, n: nat) : Msg 

    function prev_message(c: Config, a: ActorAddr, n: nat) : Msg
    {
        if n >= 1 then queue_n(c, a, n-1) else Msg.ERR
    }

    predicate WF_queue(c: Config, a: ActorAddr) {
        (forall n:nat :: n < queue_length(c,a) ==> queue_n(c, a, n) != Msg.ERR) &&
        (forall n:nat :: n >= queue_length(c,a) ==> queue_n(c,a,n) == Msg.ERR)
    }

    predicate push(c: Config, a: ActorAddr, msg: Msg, c': Config)
    {
        WF_queue(c,a) && msg != Msg.ERR &&
        queue_length(c', a) == queue_length(c, a) + 1 && queue_n(c', a, queue_length(c,a)) == msg &&
        forall n:nat :: n != queue_length(c,a) ==> queue_n(c',a,n) == queue_n(c,a,n) 
    }

    lemma push_preserves_WF_queue(c: Config, a: ActorAddr, msg: Msg, c': Config) 
        requires push(c, a, msg, c')
        ensures WF_queue(c', a)
    {
    }
    
//TODO: Complete pop
    predicate pop(c:Config, a:ActorAddr, c': Config) 
    
    datatype Capability = WRITE | READ | TAG | ERR
    type DP 
    type SP
    
    datatype Optional<T> = Some(o: T) | None 
    predicate A(c: Config, a: ActorAddr, dp: DP, i: Addr, k: Capability)
    
    predicate DFR(c: Config) {
        forall a, a': ActorAddr, p, p': DP, i: Addr, k: Capability:: 
            a != a' && 
            A(c, a, p, i, WRITE) &&
            A(c, a', p', i, k) ==> 
            k == TAG
    }

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
    
    predicate RcvApp(c: Config, a: ActorAddr, c': Config) 
        requires actor_state_idle(c, a)  
        requires queue_head_app(c, a)
    {
        actor_state_rcv(c', a) &&
        //0 here, 1 in the paper, leave which one?
        actor_ws(c', a) == set i | 
            i in allocated_addresses(c) &&
            exists mp,k ::
            mp in paths_from_message_n(c,a,0) &&
            A(c,a,mp,i,k)
    }
    
    ////REFERENCE COUNTS////
    function RC(c: Config, i: Addr, a: ActorAddr) : nat 
    function OMC(c: Config, i: Addr) : int
    function LRC(c: Config, i: Addr) : int
    function FRC(c: Config, i: Addr) : int
    function AMC(c: Config, i: Addr) : int 
    //{|(set x | exists a,k :: 0<=k<queue_length(c, a) && x==(a,k) && Reach(c,a,k,i))|}
    
    predicate Owner(c: Config, i: Addr, a: ActorAddr)
    predicate actor_state_exe(c: Config, a: ActorAddr)
    function actor_state_exe_frame(c: Config, a: ActorAddr) : Frame 
    function frame_from_app_message_n(c: Config, a: ActorAddr, n: nat) : Frame
    
    predicate RcvToExe(c: Config, a: ActorAddr, c': Config)
    {
        actor_state_rcv(c, a) &&
        queue_head_app(c, a) &&
        actor_state_exe(c', a) && 
        actor_state_exe_frame(c', a) == frame_from_app_message_n(c,a,0) &&
        pop(c,a,c') &&
        (forall i :: i in actor_ws(c,a) && Owner(c, i, a) ==> RC(c', i, a) == RC(c, i, a) - 1) &&
        (forall i :: i in actor_ws(c,a) && !Owner(c, i, a) ==> RC(c', i, a) == RC(c, i, a) + 1) &&
        (forall i :: i !in actor_ws(c,a) ==> RC(c', i, a) == RC(c, i, a)) &&
        //TODO: TAKE THIS OUT INTO OWNERSHIP_PRESERVED(C)
        (forall i, a' :: Owner(c,i,a') == Owner(c',i,a')) &&
        (forall i, a' :: a' != a ==> RC(c', i, a') == RC(c, i, a'))
    } 

    lemma RcvToExe_Increases_A(c: Config, a: ActorAddr, c': Config)
        requires RcvToExe(c, a, c')
        ensures forall lp, i, k :: A(c, a, lp, i, k) ==> A(c', a, lp, i, k)
        ensures forall lp, i, k :: A(c', a, lp, i, k) ==> A(c, a, lp, i, k) || i in actor_ws(c, a)
        ensures forall lp, i, k, a' :: a' != a ==> A(c', a', lp, i, k) == A(c, a', lp, i, k)
    
    ////INVARIANTS////
    predicate INV_2(c: Config) 
    /*
    {
        forall i, p, k :: 
            (A(c, a, p, i, k) &&
            !Owner(c, i, a)) || 
            Owner(c,i,a') && 
            A(c, a', p, i, k) ==> 
            LRC(c,i)
    }*/
    predicate INV_3(c: Config) {
        forall i, lp, k, a :: A(c, a, lp, i, k) && !Owner(c, i, a) ==> RC(c, i, a) > 0
    }

    lemma RcvToExe_preserves_INV_3(c: Config, a': ActorAddr, c': Config) 
        requires INV_3(c) 
        requires RcvToExe(c, a', c')
        ensures INV_3(c')
    {
        RcvToExe_Increases_A(c, a', c');
        forall i, lp, k, a | A(c', a, lp, i, k) &&
                          !Owner(c, i ,a)
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
/*
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
  */  

} 
