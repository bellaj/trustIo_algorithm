globals[
  time
  total_global_transactions ;  the global number of transactions
  number_of_nodes;
  current_ticks;
  number_of_malicous_nodes
  number_of_good_nodes
  security_treshold ; to vote trust score should be > security_treshold
  successful_transactions;
  Gamma ; convergence treshold
]
;globals variables hold values that are accessible anywhere in th program
;link parameters
links-own [
  feedback_weight ; total sum of feedbacks between 2 peers
  No_malicious_transaction_between_src_dest
  total_transaction_between_src_dest
  local_trust_ ; Normalized local trust between 2 peers
]
;;peer's parameters
turtles-own [
  security_score
  User_behavior
  service               ;;each node offer a certian number of services, we will use just 0 or 1
  total_transactions    ;;N of tx performed by the peer
  ;peer_trust_value        ;;peers label
  malicious             ;;is the peer malicious or not?
  
  list_other_peer_id ; a list of peers that the peers rated
  list_in_peer_id ; a list of peers that rated the current peer
  
  global_trust_value; GT(P)
  trust_score; T(P)
]


to setup
  settings-initialization
  clear-all                       ;; clear everything on canvas
  setup-nodes                     ;; a procedure to set nodes
  ;setup-edges                     ;; a procedure to set edges
  setup-malicious-nodes
  ;ask turtles [ set color red]   ;; paint nodes red
  ask links [set color white]     ;; paint edges white
  reset-ticks
  layout
end
;--------------------------------------
;Network intialization
;-------------------------------------
to setup-nodes
  set-default-shape turtles "circle"
  set number_of_nodes number_of_peers ;number_peers is defined in the interface
  create-turtles number_of_nodes
  ask turtles
  [
    set color green
    set size 1.2

    ;;set service
    set service random 2;no_services_available ;either it provides the service or not !!2not1

    ;;initialise the initial trust values
    set global_trust_value global_initial_trust_value
    set trust_score global_initial_trust_value

    ;;set the label for the nodes
    set label precision global_trust_value 2 ;1.25 2 digits after .
 

    ;;set malicious status
    set malicious false

    ; for visual reasons, we don't put any nodes *too* close to the edges
    ;setxy (random-xcor * 0.95) (random-ycor * 0.95)
    
    initialize-turtle-lists self; initialize turtles lists and vars
  ]
  
 

end

to setup-malicious-nodes
    ;;set malicious peers according to percentage
  let n_malicious round ((number_of_nodes * number_of_malicious_nodes) / 100) ; malicious_peers % defined in the interface

  let malicious_peers_set n-of n_malicious turtles
  ask malicious_peers_set
  [
    set color red
    set malicious true
  ]


  ;;calculate number of malicous nodes in the network
  set number_of_malicous_nodes n_malicious
  ;;calculate number of good nodes
  set number_of_good_nodes number_of_nodes - number_of_malicous_nodes  
  show word "number of malicious peers :" number_of_malicous_nodes
end



to setup-edges
  let num-links  6

  while [ count links < num-links ] ;; num-links given by the user from interface
  [
    ask one-of turtles
    [
      let other_turtle one-of other turtles

      if other_turtle != nobody [ create-link-to other_turtle ]
      ask link-with other_turtle [
        set feedback_weight 10
        ;set label feedback_weight
       
      ]
      show word " new link:" link-with other_turtle
      ask link-with other_turtle[
          if feedback_weight = 0 ; for unkonw reason weight for some links isn't set in the previous operation
          [
          show word "error weigh detected and corrected" other_turtle
          set feedback_weight 10
          
        ]
          show word "wieight is" feedback_weight
      ]
    ]
  ]
    ; make the network look a little prettier
    repeat 10
    [
      layout-spring turtles links 0.3 (world-width / (sqrt number_of_nodes)) 1
    ]
end


;--------------------------------------
; Initialition and entrypoint
;-------------------------------------
to settings-initialization
  set security_treshold 0.2
  set Gamma 0.001 ; to modify treshold of confergence
end

to initialize-turtle-lists [peer]
  ;;initialise feedback lists
  set list_other_peer_id []
  set list_in_peer_id []

end


to go

  
  if not any? turtles [stop] ;exits if there are no more turtles
 
  set current_ticks ticks
  show "---------------------------------"
  show word "the current tick " current_ticks
  show "---------------------------------"
  transact
  update_trust
  ;layout
  tick
end

;--------------------------------------
; Functions
;-------------------------------------
to transact
  
  let peer1 one-of turtles   ; will request a service from another peer
  
  
  if evaluate-connections [ ;=> this might disturb the calcul if the GT is not alreaady calculated as it will remove links between peers
   evaluate-current-connections peer1
    ]
  
  
   let potential_partners_list find-potential_peers-to-connect-with 1 [who] of peer1  ;nodes providing the service
  
   print (word "==> potential_partners_list of" peer1 " are " potential_partners_list )
 
    ;;check if there are items in the list
    let peer2 0 ; will host the other peer who provides the service

    ifelse length potential_partners_list < 1
    [
      stop ;;exit the procedure
    ]
    [
      ;;select a random peer
    ifelse choose_random_or_most_trusted ; defined in the interface => choose most ranked node or at random
    [
      set peer2 item random (length potential_partners_list) potential_partners_list
    ]
    [
      set peer2 item 0 potential_partners_list ;;set the chosen peer to the most trusted peer
    ]
   
      ;;final check
      if [who] of peer1 = [who] of peer2
      [
        stop ;;exit the procedure
        show " ERROR!!!!!! exiting for equality reason"
      ]
    ]

    ;;perform the transaction between two peers
    perform-transaction-and-rate peer1 peer2
  
    ;compute-global-trust peer2
end

;not mine
;;evaluates all the connections of a peer
;;the link is removed if the nodes trust value is below the threshold
to evaluate-current-connections [peer]
  ask peer
  [
    ask my-links ;the agentset containing all links
    [
      if [global_trust_value] of other-end < trust_threshold
      [
        die ; ceases to exist
      ]
    ]
  ]
end

;Not mine
;;finding peers who offer the desired service
;;returns a list of the top [no_peers_to_return] peers
to-report find-potential_peers-to-connect-with [required-service peerid] ; required-service is a parameter, the number of possible services is defined in the interface ==> here the random walk should be performed
  let potential_peers other turtles with [service = required-service and who != peerid ] ; add and trust_score > trust_treshold
   
  let no_peers_to_return  number_of_peers - 1
  let sorted_list 0
  ;;return number of peers
  ifelse count potential_peers >= no_peers_to_return ;;list is small than number that needs to be returned
  [
    ;;sort the list and return only the first [no_peers_to_return]
    set sorted_list sublist ( sort-on [( - global_trust_value)] potential_peers ) 0 no_peers_to_return
  ]
  [
    ;;sort the entire list
    set sorted_list sort-on [(- global_trust_value)] potential_peers
  ]

  report sorted_list
end

;;this method performs the transaction part of a collaboration
to perform-transaction-and-rate [peer1 peer2]   ; Transaction is from peer2 to peer1

  ;;get the id of origional node
  let peer1_id [who] of peer1 ; destination
  ;;get the id of other node
  let peer2_id [who] of peer2 ; source

  ;;get the exact time of the transaction
  let time_of_transaction current_ticks
   

  ;;determing if any of the peers will act maliciously during this transaction
  ;let peer1_act_maliciously true
  let peer2_act_maliciously true

  if [malicious] of peer2 ;;this peer is malicious ; it gives only malicious tx
    [
    ;if random 101 <= malicious_transactions_percentage ; % defined by interface and < 100
    ; [    
      set peer2_act_maliciously true 
    ;]
    ]
  
 if not [malicious] of peer2 ;;this peer is malicious ;; IMO malicious peers can act or not maliciously
    [
      ifelse random 101 <= malicious_transactions_percentage ; % defined by interface and < 100
      [    set peer2_act_maliciously true      ]
      [    set peer2_act_maliciously false     ]
    ]
   
  show word "=> peer2 will act (false) in case 0% set " peer2_act_maliciously
 
  ;;perform actions via peer1
  ask turtle peer1_id
  [
   print (word "==> peer " peer1 "requests tx from" peer2 )
   ;;update origional peer (peer1) feedback history based on the feedback from peer2
   
    ifelse peer2_act_maliciously     [ setup-feedback_edges_between peer1 peer2 -1 ]
    [ setup-feedback_edges_between peer1 peer2 1 ]
    
    
     ask link-with peer2 [
       if peer2_act_maliciously
      [     
        set No_malicious_transaction_between_src_dest No_malicious_transaction_between_src_dest + 1 ; one more malicious tx
      ]
      set total_transaction_between_src_dest total_transaction_between_src_dest + 1
      
    ]
    
    compute-local-trust peer1 peer2
   
    set total_transactions total_transactions + 1
  
 
   ]

  
  set total_global_transactions total_global_transactions + 1
end



to setup-feedback_edges_between [peer1 peer2 feedback] ; P1 => P2 
  
 
    ask peer1
    [
      let other_turtle peer2
     if other_turtle = nobody
     [stop]
    
      if link-with other_turtle = nobody  ; create new link
      [ 
      create-link-to other_turtle
      show "======================================" 
      show word " ==> new link:" link-with other_turtle
      show "======================================" 
         ]

    
    
      ask link-with other_turtle [
        let original_feedback feedback_weight
        set feedback_weight feedback_weight + feedback

          if feedback_weight = original_feedback ; for unkonw reason feedback_weight for some links isn't set in the previous operation
          [
          show word "error weigh detected and corrected" other_turtle
          set feedback_weight feedback_weight + feedback
          
        ]
           
      ]
      
        if  not member? peer2 list_other_peer_id[set list_other_peer_id lput other_turtle list_other_peer_id]
    
        ask other_turtle[
        if  not member? peer1 list_in_peer_id ;here
        [set list_in_peer_id lput peer1 list_in_peer_id]
        ]
   
    ]

    ; make the network look a little prettier
    repeat 10
    [
      layout-spring turtles links 0.3 (world-width / (sqrt number_of_nodes)) 1
    ]
end

to compute-local-trust [peer1 peer2]  ;local trust that peer1 has in 2
  
  let sigma_sum 0
  
   ask peer1
  [
    ask my-links ;the agentset containing all links
    [

      if feedback_weight > 0 [
      set sigma_sum sigma_sum + feedback_weight
      ]
      
    ]

    ask link-with peer2 [
      if total_transaction_between_src_dest > 0
      [
      ifelse feedback_weight > 0 [
      let sum_p_q feedback_weight
      let AR_p_q   (total_transaction_between_src_dest - No_malicious_transaction_between_src_dest) / total_transaction_between_src_dest
      set sum_p_q sum_p_q * AR_p_q
      let LTR  precision  ((sum_p_q / sigma_sum) ) 2
      set  local_trust_ LTR
           
      ;show word "==>> local trust" local_trust_
      set label  local_trust_ 
        ]
        [
          set label 0
        ]
      ]
    ]
  ]
end

;-------------------------------
;Global trust computation
;--------------------------------
to compute-global-trust [peer]
 
let total_trust 0.0
show word "computing GT of " peer
ask peer
[
    let GT_P global_initial_trust_value
    let GT_P' 0
 ; ask my-links ;the agentset containing all links
    let GTs []
    let sum_GT_P sum_global_trust  peer ;sum of GT of peers pointing to current peer
   print (word "====> pointing peers to " peer "are" list_in_peer_id)
   foreach list_in_peer_id
   [ ?1 ->
      ;if feedback_weight > 0 [ ]
      ;show  "computing GT of step1"
      ask  ?1 [
         
       ; set the GT of current peer
       let GT_i global_trust_value
       
        
       if link-with peer != nobody[
          ask link-with peer [
          ;show  "computing GT of step3"
        let local_trust_i local_trust_
        if sum_GT_P > 0
        [
        let GT_P_i (local_trust_i * GT_i) / (sum_GT_P)
        set GTs lput GT_P_i GTs
          ]
        ]
      ]
      ]
    ]
    
    set GT_P sum GTs 

  
    set global_trust_value GT_P
    set label precision global_trust_value 2
]


end

to-report sum_global_trust[ peer]
  let temp_sum 0
  ask peer[
 ;set old_GT sum [global_trust_value] of turtles ;
   foreach list_in_peer_id
   [ ?1 ->
    
    ask ?1[
    
     set temp_sum temp_sum + global_trust_value
    ]
    
    ]
  ]
   
  report temp_sum
end




to update_trust
  show "updating trust"
  
  let old_GT global_initial_trust_value
  let new_GT global_initial_trust_value
  
  set old_GT sum [global_trust_value] of turtles ;
    ask turtles [ ; ask all peers
    ;set old_GT lput global_trust_value old_GT
    compute-global-trust self
  ]
  set new_GT sum [global_trust_value] of turtles ;
   while [not convergence old_GT new_GT ]
    [
  set old_GT sum [global_trust_value] of turtles ;
  ask turtles [ ; ask all peers
    ;set old_GT lput global_trust_value old_GT
    compute-global-trust self
        show word "peer asked to update" self
    ;set new_GT lput global_trust_value new_GT
     
  ]
  set new_GT sum [global_trust_value] of turtles ;
  show word "the convergence old_GT" old_GT
  show word "the convergence new_GT" new_GT
  show "-------------------------------------"
    ]
end


to-report convergence [GT GT']
let converge false
  if abs(GT' - GT) <= Gamma
  [set converge true]
  show word "the convergence" abs(GT' - GT)
report converge
  
end
;----------------
;random walker
;------------------------
to walker
  ask turtles [ 
    forward 1        ;; all turtles move forward one step
    right random 360 ;; and turn a random amount
  ]
end
;-------------------------------
;Display settings
;--------------------------------
to layout
    repeat 10
    [
      layout-spring turtles links 0.3 (world-width / (sqrt number_of_nodes)) 1
    ]
end
to layout2
  ;; the number 3 here is arbitrary; more repetitions slows down the
  ;; model, but too few gives poor layouts
  repeat 3 [
    ;; the more turtles we have to fit into the same amount of space,
    ;; the smaller the inputs to layout-spring we'll need to use
    let factor sqrt count turtles
    ;; numbers here are arbitrarily chosen for pleasing appearance
    layout-spring turtles links (1 / factor) (7 / factor) (10 / factor)
    display  ;; for smooth animation
  ]
  ;; don't bump the edges of the world
  let x-offset max [xcor] of turtles + min [xcor] of turtles
  let y-offset max [ycor] of turtles + min [ycor] of turtles
  ;; big jumps look funny, so only adjust a little each time
  set x-offset limit-magnitude x-offset 0.1
  set y-offset limit-magnitude y-offset 0.1
  ask turtles [ setxy (xcor - x-offset / 2) (ycor - y-offset / 2) ]
end
to-report limit-magnitude [number limit]
  if number > limit [ report limit ]
  if number < (- limit) [ report (- limit) ]
  report number
end
