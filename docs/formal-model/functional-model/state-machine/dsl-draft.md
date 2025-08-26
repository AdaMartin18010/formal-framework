# 状态机建模DSL草案

## 1. 设计目标

- 用统一DSL描述状态机、状态转换、事件处理、条件判断等要素
- 支持自动生成状态机代码、状态图、事件处理逻辑等
- 支持嵌套状态、并行状态、历史状态、超时处理等高级特性

## 2. 基本语法结构

```dsl
state_machine "order_state_machine" {
  description: "订单状态机"
  version: "1.0.0"
  author: "system"
  
  initial_state: "pending"
  final_states: ["completed", "cancelled", "refunded"]
  
  states: [
    {
      name: "pending"
      description: "待处理状态"
      entry_actions: ["notify_pending"]
      exit_actions: ["log_state_change"]
      allowed_events: ["confirm", "cancel"]
    },
    {
      name: "confirmed"
      description: "已确认状态"
      entry_actions: ["prepare_shipping"]
      exit_actions: ["log_state_change"]
      allowed_events: ["ship", "cancel"]
    },
    {
      name: "shipped"
      description: "已发货状态"
      entry_actions: ["start_delivery_tracking"]
      exit_actions: ["log_state_change"]
      allowed_events: ["deliver", "return"]
    },
    {
      name: "delivered"
      description: "已送达状态"
      entry_actions: ["start_completion_timer"]
      exit_actions: ["log_state_change"]
      allowed_events: ["complete", "return"]
    },
    {
      name: "completed"
      description: "已完成状态"
      entry_actions: ["finalize_order"]
      final: true
    },
    {
      name: "cancelled"
      description: "已取消状态"
      entry_actions: ["process_cancellation"]
      final: true
    },
    {
      name: "returned"
      description: "已退货状态"
      entry_actions: ["process_return_request"]
      allowed_events: ["refund"]
    },
    {
      name: "refunded"
      description: "已退款状态"
      entry_actions: ["finalize_refund"]
      final: true
    }
  ]
  
  transitions: [
    {
      from: "pending"
      to: "confirmed"
      event: "confirm"
      condition: "can_confirm_order(order_id)"
      actions: ["validate_order", "notify_confirmation"]
    },
    {
      from: "pending"
      to: "cancelled"
      event: "cancel"
      condition: "can_cancel_order(order_id)"
      actions: ["cancel_order", "notify_cancellation"]
    },
    {
      from: "confirmed"
      to: "shipped"
      event: "ship"
      condition: "inventory_available(order_id)"
      actions: ["prepare_shipment", "update_inventory"]
    },
    {
      from: "confirmed"
      to: "cancelled"
      event: "cancel"
      condition: "can_cancel_order(order_id)"
      actions: ["cancel_order", "restore_inventory"]
    },
    {
      from: "shipped"
      to: "delivered"
      event: "deliver"
      condition: "delivery_confirmed(order_id)"
      actions: ["complete_delivery", "notify_delivery"]
    },
    {
      from: "shipped"
      to: "returned"
      event: "return"
      condition: "return_requested(order_id)"
      actions: ["process_return", "notify_return"]
    },
    {
      from: "delivered"
      to: "completed"
      event: "complete"
      condition: "completion_confirmed(order_id)"
      actions: ["complete_order", "send_feedback_request"]
    },
    {
      from: "delivered"
      to: "returned"
      event: "return"
      condition: "return_requested(order_id)"
      actions: ["process_return", "notify_return"]
    },
    {
      from: "returned"
      to: "refunded"
      event: "refund"
      condition: "refund_processed(order_id)"
      actions: ["process_refund", "notify_refund"]
    }
  ]
  
  error_handling: {
    invalid_transition: {
      action: "log_error"
      message: "无效的状态转换"
    },
    condition_failed: {
      action: "notify_user"
      message: "操作条件不满足"
    },
    system_error: {
      action: "log_error_and_notify_admin"
      message: "系统错误"
    }
  }
  
  monitoring: {
    metrics: [
      "state_transition_count",
      "state_duration",
      "error_count"
    ],
    alerts: [
      {
        condition: "state_duration > 24h"
        action: "notify_admin"
        message: "状态停留时间过长"
      }
    ]
  }
}
```

## 3. 关键元素

- state_machine：状态机声明
- description：描述信息
- version：版本号
- author：作者
- initial_state：初始状态
- final_states：最终状态列表
- states：状态定义
- transitions：状态转换定义
- error_handling：错误处理
- monitoring：监控配置

## 4. 高级用法

### 4.1 嵌套状态

```dsl
state_machine "complex_order_state_machine" {
  description: "复杂订单状态机"
  version: "1.0.0"
  
  initial_state: "processing"
  
  states: [
    {
      name: "processing"
      description: "处理中状态"
      composite: true
      states: [
        {
          name: "pending"
          description: "待处理"
          entry_actions: ["notify_pending"]
        },
        {
          name: "confirmed"
          description: "已确认"
          entry_actions: ["prepare_shipping"]
        }
      ]
      transitions: [
        {
          from: "pending"
          to: "confirmed"
          event: "confirm"
          condition: "can_confirm_order(order_id)"
        }
      ]
    },
    {
      name: "shipping"
      description: "配送中状态"
      composite: true
      states: [
        {
          name: "shipped"
          description: "已发货"
          entry_actions: ["start_delivery_tracking"]
        },
        {
          name: "in_transit"
          description: "运输中"
          entry_actions: ["update_tracking"]
        }
      ]
      transitions: [
        {
          from: "shipped"
          to: "in_transit"
          event: "start_transit"
        },
        {
          from: "in_transit"
          to: "delivered"
          event: "deliver"
          condition: "delivery_confirmed(order_id)"
        }
      ]
    },
    {
      name: "completed"
      description: "已完成状态"
      final: true
    }
  ]
  
  transitions: [
    {
      from: "processing"
      to: "shipping"
      event: "ship"
      condition: "inventory_available(order_id)"
    },
    {
      from: "shipping"
      to: "completed"
      event: "complete"
      condition: "completion_confirmed(order_id)"
    }
  ]
}
```

### 4.2 并行状态

```dsl
state_machine "parallel_order_state_machine" {
  description: "并行订单状态机"
  version: "1.0.0"
  
  initial_state: "active"
  
  states: [
    {
      name: "active"
      description: "活跃状态"
      parallel: true
      regions: [
        {
          name: "payment_region"
          states: [
            {
              name: "unpaid"
              description: "未支付"
              transitions: [
                {
                  to: "paid"
                  event: "payment_success"
                }
              ]
            },
            {
              name: "paid"
              description: "已支付"
            }
          ]
        },
        {
          name: "inventory_region"
          states: [
            {
              name: "checking"
              description: "检查中"
              transitions: [
                {
                  to: "reserved"
                  event: "inventory_available"
                },
                {
                  to: "unavailable"
                  event: "inventory_unavailable"
                }
              ]
            },
            {
              name: "reserved"
              description: "已预留"
            },
            {
              name: "unavailable"
              description: "库存不足"
            }
          ]
        }
      ]
    },
    {
      name: "completed"
      description: "已完成状态"
      final: true
    }
  ]
  
  transitions: [
    {
      from: "active"
      to: "completed"
      event: "complete"
      condition: "all_regions_completed()"
    }
  ]
}
```

### 4.3 历史状态

```dsl
state_machine "history_state_machine" {
  description: "历史状态机"
  version: "1.0.0"
  
  initial_state: "idle"
  
  states: [
    {
      name: "idle"
      description: "空闲状态"
      transitions: [
        {
          to: "working"
          event: "start_work"
        }
      ]
    },
    {
      name: "working"
      description: "工作状态"
      composite: true
      history: "deep"
      states: [
        {
          name: "processing"
          description: "处理中"
          transitions: [
            {
              to: "paused"
              event: "pause"
            },
            {
              to: "completed"
              event: "finish"
            }
          ]
        },
        {
          name: "paused"
          description: "暂停中"
          transitions: [
            {
              to: "processing"
              event: "resume"
            }
          ]
        },
        {
          name: "completed"
          description: "已完成"
        }
      ]
      transitions: [
        {
          to: "idle"
          event: "stop"
        }
      ]
    }
  ]
}
```

### 4.4 超时处理

```dsl
state_machine "timeout_state_machine" {
  description: "超时状态机"
  version: "1.0.0"
  
  initial_state: "waiting"
  
  states: [
    {
      name: "waiting"
      description: "等待状态"
      timeout: {
        duration: "30s"
        action: "timeout_handler"
        target_state: "timeout"
      }
      transitions: [
        {
          to: "processing"
          event: "start"
        }
      ]
    },
    {
      name: "processing"
      description: "处理状态"
      timeout: {
        duration: "5m"
        action: "processing_timeout"
        target_state: "error"
      }
      transitions: [
        {
          to: "completed"
          event: "finish"
        }
      ]
    },
    {
      name: "completed"
      description: "已完成状态"
      final: true
    },
    {
      name: "timeout"
      description: "超时状态"
      final: true
    },
    {
      name: "error"
      description: "错误状态"
      final: true
    }
  ]
}
```

## 5. 代码生成模板

### 5.1 Java状态机生成

```java
// OrderStateMachine.java
public class OrderStateMachine {
    
    private OrderState currentState;
    private final OrderService orderService;
    private final NotificationService notificationService;
    
    public OrderStateMachine(OrderService orderService, NotificationService notificationService) {
        this.orderService = orderService;
        this.notificationService = notificationService;
        this.currentState = OrderState.PENDING;
    }
    
    public boolean transition(String event, int orderId) {
        try {
            switch (currentState) {
                case PENDING:
                    return handlePendingState(event, orderId);
                case CONFIRMED:
                    return handleConfirmedState(event, orderId);
                case SHIPPED:
                    return handleShippedState(event, orderId);
                case DELIVERED:
                    return handleDeliveredState(event, orderId);
                case RETURNED:
                    return handleReturnedState(event, orderId);
                default:
                    return false;
            }
        } catch (Exception e) {
            logError("状态转换失败", e);
            return false;
        }
    }
    
    private boolean handlePendingState(String event, int orderId) {
        switch (event) {
            case "confirm":
                if (canConfirmOrder(orderId)) {
                    validateOrder(orderId);
                    notifyConfirmation(orderId);
                    currentState = OrderState.CONFIRMED;
                    return true;
                }
                break;
            case "cancel":
                if (canCancelOrder(orderId)) {
                    cancelOrder(orderId);
                    notifyCancellation(orderId);
                    currentState = OrderState.CANCELLED;
                    return true;
                }
                break;
        }
        return false;
    }
    
    private boolean handleConfirmedState(String event, int orderId) {
        switch (event) {
            case "ship":
                if (inventoryAvailable(orderId)) {
                    prepareShipment(orderId);
                    updateInventory(orderId);
                    currentState = OrderState.SHIPPED;
                    return true;
                }
                break;
            case "cancel":
                if (canCancelOrder(orderId)) {
                    cancelOrder(orderId);
                    restoreInventory(orderId);
                    currentState = OrderState.CANCELLED;
                    return true;
                }
                break;
        }
        return false;
    }
    
    // 其他状态处理方法...
    
    private boolean canConfirmOrder(int orderId) {
        return orderService.canConfirmOrder(orderId);
    }
    
    private boolean canCancelOrder(int orderId) {
        return orderService.canCancelOrder(orderId);
    }
    
    private boolean inventoryAvailable(int orderId) {
        return orderService.inventoryAvailable(orderId);
    }
    
    private void validateOrder(int orderId) {
        orderService.validateOrder(orderId);
    }
    
    private void notifyConfirmation(int orderId) {
        notificationService.notifyConfirmation(orderId);
    }
    
    private void cancelOrder(int orderId) {
        orderService.cancelOrder(orderId);
    }
    
    private void notifyCancellation(int orderId) {
        notificationService.notifyCancellation(orderId);
    }
    
    private void prepareShipment(int orderId) {
        orderService.prepareShipment(orderId);
    }
    
    private void updateInventory(int orderId) {
        orderService.updateInventory(orderId);
    }
    
    private void restoreInventory(int orderId) {
        orderService.restoreInventory(orderId);
    }
    
    private void logError(String message, Exception e) {
        // 错误日志记录
    }
}
```

### 5.2 Python状态机生成

```python
# order_state_machine.py
from enum import Enum
from typing import Dict, Any

class OrderState(Enum):
    PENDING = "pending"
    CONFIRMED = "confirmed"
    SHIPPED = "shipped"
    DELIVERED = "delivered"
    COMPLETED = "completed"
    CANCELLED = "cancelled"
    RETURNED = "returned"
    REFUNDED = "refunded"

class OrderStateMachine:
    
    def __init__(self, order_service, notification_service):
        self.current_state = OrderState.PENDING
        self.order_service = order_service
        self.notification_service = notification_service
        
        # 状态转换表
        self.transitions = {
            OrderState.PENDING: {
                'confirm': self._handle_confirm,
                'cancel': self._handle_cancel
            },
            OrderState.CONFIRMED: {
                'ship': self._handle_ship,
                'cancel': self._handle_cancel
            },
            OrderState.SHIPPED: {
                'deliver': self._handle_deliver,
                'return': self._handle_return
            },
            OrderState.DELIVERED: {
                'complete': self._handle_complete,
                'return': self._handle_return
            },
            OrderState.RETURNED: {
                'refund': self._handle_refund
            }
        }
    
    def transition(self, event: str, order_id: int) -> bool:
        try:
            if event in self.transitions.get(self.current_state, {}):
                handler = self.transitions[self.current_state][event]
                return handler(order_id)
            return False
        except Exception as e:
            self._log_error("状态转换失败", e)
            return False
    
    def _handle_confirm(self, order_id: int) -> bool:
        if self.order_service.can_confirm_order(order_id):
            self.order_service.validate_order(order_id)
            self.notification_service.notify_confirmation(order_id)
            self.current_state = OrderState.CONFIRMED
            return True
        return False
    
    def _handle_cancel(self, order_id: int) -> bool:
        if self.order_service.can_cancel_order(order_id):
            self.order_service.cancel_order(order_id)
            self.notification_service.notify_cancellation(order_id)
            self.current_state = OrderState.CANCELLED
            return True
        return False
    
    def _handle_ship(self, order_id: int) -> bool:
        if self.order_service.inventory_available(order_id):
            self.order_service.prepare_shipment(order_id)
            self.order_service.update_inventory(order_id)
            self.current_state = OrderState.SHIPPED
            return True
        return False
    
    def _handle_deliver(self, order_id: int) -> bool:
        if self.order_service.delivery_confirmed(order_id):
            self.order_service.complete_delivery(order_id)
            self.notification_service.notify_delivery(order_id)
            self.current_state = OrderState.DELIVERED
            return True
        return False
    
    def _handle_complete(self, order_id: int) -> bool:
        if self.order_service.completion_confirmed(order_id):
            self.order_service.complete_order(order_id)
            self.notification_service.send_feedback_request(order_id)
            self.current_state = OrderState.COMPLETED
            return True
        return False
    
    def _handle_return(self, order_id: int) -> bool:
        if self.order_service.return_requested(order_id):
            self.order_service.process_return(order_id)
            self.notification_service.notify_return(order_id)
            self.current_state = OrderState.RETURNED
            return True
        return False
    
    def _handle_refund(self, order_id: int) -> bool:
        if self.order_service.refund_processed(order_id):
            self.order_service.process_refund(order_id)
            self.notification_service.notify_refund(order_id)
            self.current_state = OrderState.REFUNDED
            return True
        return False
    
    def _log_error(self, message: str, error: Exception):
        # 错误日志记录
        pass
```

### 5.3 JavaScript状态机生成

```javascript
// orderStateMachine.js
class OrderStateMachine {
    
    constructor(orderService, notificationService) {
        this.currentState = 'pending';
        this.orderService = orderService;
        this.notificationService = notificationService;
        
        // 状态转换表
        this.transitions = {
            pending: {
                confirm: this.handleConfirm.bind(this),
                cancel: this.handleCancel.bind(this)
            },
            confirmed: {
                ship: this.handleShip.bind(this),
                cancel: this.handleCancel.bind(this)
            },
            shipped: {
                deliver: this.handleDeliver.bind(this),
                return: this.handleReturn.bind(this)
            },
            delivered: {
                complete: this.handleComplete.bind(this),
                return: this.handleReturn.bind(this)
            },
            returned: {
                refund: this.handleRefund.bind(this)
            }
        };
    }
    
    transition(event, orderId) {
        try {
            if (this.transitions[this.currentState] && 
                this.transitions[this.currentState][event]) {
                const handler = this.transitions[this.currentState][event];
                return handler(orderId);
            }
            return false;
        } catch (error) {
            this.logError("状态转换失败", error);
            return false;
        }
    }
    
    async handleConfirm(orderId) {
        if (await this.orderService.canConfirmOrder(orderId)) {
            await this.orderService.validateOrder(orderId);
            await this.notificationService.notifyConfirmation(orderId);
            this.currentState = 'confirmed';
            return true;
        }
        return false;
    }
    
    async handleCancel(orderId) {
        if (await this.orderService.canCancelOrder(orderId)) {
            await this.orderService.cancelOrder(orderId);
            await this.notificationService.notifyCancellation(orderId);
            this.currentState = 'cancelled';
            return true;
        }
        return false;
    }
    
    async handleShip(orderId) {
        if (await this.orderService.inventoryAvailable(orderId)) {
            await this.orderService.prepareShipment(orderId);
            await this.orderService.updateInventory(orderId);
            this.currentState = 'shipped';
            return true;
        }
        return false;
    }
    
    async handleDeliver(orderId) {
        if (await this.orderService.deliveryConfirmed(orderId)) {
            await this.orderService.completeDelivery(orderId);
            await this.notificationService.notifyDelivery(orderId);
            this.currentState = 'delivered';
            return true;
        }
        return false;
    }
    
    async handleComplete(orderId) {
        if (await this.orderService.completionConfirmed(orderId)) {
            await this.orderService.completeOrder(orderId);
            await this.notificationService.sendFeedbackRequest(orderId);
            this.currentState = 'completed';
            return true;
        }
        return false;
    }
    
    async handleReturn(orderId) {
        if (await this.orderService.returnRequested(orderId)) {
            await this.orderService.processReturn(orderId);
            await this.notificationService.notifyReturn(orderId);
            this.currentState = 'returned';
            return true;
        }
        return false;
    }
    
    async handleRefund(orderId) {
        if (await this.orderService.refundProcessed(orderId)) {
            await this.orderService.processRefund(orderId);
            await this.notificationService.notifyRefund(orderId);
            this.currentState = 'refunded';
            return true;
        }
        return false;
    }
    
    logError(message, error) {
        // 错误日志记录
        console.error(message, error);
    }
}
```

## 6. 验证规则

### 6.1 语法验证规则

```yaml
validation:
  required_fields:
    - state_machine.name
    - state_machine.description
    - state_machine.version
    - state_machine.initial_state
    - state_machine.states
    - state_machine.transitions
  
  type_constraints:
    - field: "state_machine.name"
      type: "string"
      pattern: "^[a-zA-Z_][a-zA-Z0-9_]*$"
    - field: "state_machine.version"
      type: "string"
      pattern: "^[0-9]+\\.[0-9]+\\.[0-9]+$"
    - field: "state_machine.states"
      type: "array"
      min_items: 1
    - field: "state_machine.transitions"
      type: "array"
      min_items: 1
  
  business_rules:
    - rule: "state machine name must be unique"
    - rule: "initial state must exist in states"
    - rule: "final states must exist in states"
    - rule: "transition source and target states must exist"
```

### 6.2 状态机验证规则

```yaml
state_machine_validation:
  state_consistency:
    - rule: "all states must have unique names"
    - rule: "final states must not have outgoing transitions"
    - rule: "initial state must not have incoming transitions"
  
  transition_validation:
    - rule: "all transitions must have valid source and target states"
    - rule: "transition conditions must be valid expressions"
    - rule: "transition actions must be valid function calls"
  
  error_handling:
    - rule: "all error scenarios must be handled"
    - rule: "error messages must be user-friendly"
    - rule: "timeout mechanisms must be defined for long-running states"
```

## 7. 最佳实践

### 7.1 状态机设计模式

```dsl
# 简单状态机模式
state_machine "simple_state_machine" {
  description: "简单状态机"
  
  initial_state: "start"
  final_states: ["end"]
  
  states: [
    {
      name: "start"
      description: "开始状态"
    },
    {
      name: "end"
      description: "结束状态"
      final: true
    }
  ]
  
  transitions: [
    {
      from: "start"
      to: "end"
      event: "finish"
    }
  ]
}

# 复杂状态机模式
state_machine "complex_state_machine" {
  description: "复杂状态机"
  
  initial_state: "idle"
  final_states: ["completed", "error"]
  
  states: [
    {
      name: "idle"
      description: "空闲状态"
      entry_actions: ["initialize"]
      exit_actions: ["cleanup"]
    },
    {
      name: "processing"
      description: "处理状态"
      composite: true
      states: [
        {
          name: "step1"
          description: "步骤1"
        },
        {
          name: "step2"
          description: "步骤2"
        }
      ]
    },
    {
      name: "completed"
      description: "已完成状态"
      final: true
    },
    {
      name: "error"
      description: "错误状态"
      final: true
    }
  ]
  
  transitions: [
    {
      from: "idle"
      to: "processing"
      event: "start"
      condition: "can_start()"
    },
    {
      from: "processing"
      to: "completed"
      event: "finish"
      condition: "all_steps_completed()"
    },
    {
      from: "*"
      to: "error"
      event: "error"
      condition: "has_error()"
    }
  ]
}
```

### 7.2 状态机命名规范

```dsl
# 推荐命名模式
state_machine "entity_state_machine" {
  # 实体_状态机
}

state_machine "process_state_machine" {
  # 过程_状态机
}

state_machine "workflow_state_machine" {
  # 工作流_状态机
}
```

## 8. 与主流标准的映射

| DSL元素 | UML State Machine | Spring Statemachine | XState | AWS Step Functions |
|---------|-------------------|---------------------|--------|-------------------|
| state_machine | state machine | state machine | machine | state machine |
| states | states | states | states | states |
| transitions | transitions | transitions | transitions | transitions |
| events | events | events | events | events |
| conditions | guards | guards | guards | conditions |
| actions | actions | actions | actions | actions |

## 9. 工程实践示例

```dsl
# 电商订单状态机示例
state_machine "ecommerce_order_state_machine" {
  description: "电商订单状态机"
  version: "1.0.0"
  author: "system"
  
  initial_state: "pending"
  final_states: ["completed", "cancelled", "refunded"]
  
  states: [
    {
      name: "pending"
      description: "待处理状态"
      entry_actions: ["notify_pending"]
      exit_actions: ["log_state_change"]
      allowed_events: ["confirm", "cancel"]
      timeout: {
        duration: "24h"
        action: "auto_cancel"
        target_state: "cancelled"
      }
    },
    {
      name: "confirmed"
      description: "已确认状态"
      entry_actions: ["prepare_shipping"]
      exit_actions: ["log_state_change"]
      allowed_events: ["ship", "cancel"]
    },
    {
      name: "shipped"
      description: "已发货状态"
      entry_actions: ["start_delivery_tracking"]
      exit_actions: ["log_state_change"]
      allowed_events: ["deliver", "return"]
      timeout: {
        duration: "7d"
        action: "escalate_delivery"
        target_state: "shipped"
      }
    },
    {
      name: "delivered"
      description: "已送达状态"
      entry_actions: ["start_completion_timer"]
      exit_actions: ["log_state_change"]
      allowed_events: ["complete", "return"]
      timeout: {
        duration: "14d"
        action: "auto_complete"
        target_state: "completed"
      }
    },
    {
      name: "completed"
      description: "已完成状态"
      entry_actions: ["finalize_order"]
      final: true
    },
    {
      name: "cancelled"
      description: "已取消状态"
      entry_actions: ["process_cancellation"]
      final: true
    },
    {
      name: "returned"
      description: "已退货状态"
      entry_actions: ["process_return_request"]
      allowed_events: ["refund"]
    },
    {
      name: "refunded"
      description: "已退款状态"
      entry_actions: ["finalize_refund"]
      final: true
    }
  ]
  
  transitions: [
    {
      from: "pending"
      to: "confirmed"
      event: "confirm"
      condition: "can_confirm_order(order_id)"
      actions: ["validate_order", "notify_confirmation"]
    },
    {
      from: "pending"
      to: "cancelled"
      event: "cancel"
      condition: "can_cancel_order(order_id)"
      actions: ["cancel_order", "notify_cancellation"]
    },
    {
      from: "confirmed"
      to: "shipped"
      event: "ship"
      condition: "inventory_available(order_id)"
      actions: ["prepare_shipment", "update_inventory"]
    },
    {
      from: "confirmed"
      to: "cancelled"
      event: "cancel"
      condition: "can_cancel_order(order_id)"
      actions: ["cancel_order", "restore_inventory"]
    },
    {
      from: "shipped"
      to: "delivered"
      event: "deliver"
      condition: "delivery_confirmed(order_id)"
      actions: ["complete_delivery", "notify_delivery"]
    },
    {
      from: "shipped"
      to: "returned"
      event: "return"
      condition: "return_requested(order_id)"
      actions: ["process_return", "notify_return"]
    },
    {
      from: "delivered"
      to: "completed"
      event: "complete"
      condition: "completion_confirmed(order_id)"
      actions: ["complete_order", "send_feedback_request"]
    },
    {
      from: "delivered"
      to: "returned"
      event: "return"
      condition: "return_requested(order_id)"
      actions: ["process_return", "notify_return"]
    },
    {
      from: "returned"
      to: "refunded"
      event: "refund"
      condition: "refund_processed(order_id)"
      actions: ["process_refund", "notify_refund"]
    }
  ]
  
  error_handling: {
    invalid_transition: {
      action: "log_error"
      message: "无效的状态转换"
    },
    condition_failed: {
      action: "notify_user"
      message: "操作条件不满足"
    },
    system_error: {
      action: "log_error_and_notify_admin"
      message: "系统错误"
    }
  }
  
  monitoring: {
    metrics: [
      "state_transition_count",
      "state_duration",
      "error_count",
      "timeout_count"
    ],
    alerts: [
      {
        condition: "state_duration > 24h"
        action: "notify_admin"
        message: "状态停留时间过长"
      },
      {
        condition: "error_count > 10"
        action: "notify_admin"
        message: "状态机错误次数过多"
      }
    ]
  }
}
```

这个DSL设计为状态机建模提供了完整的配置语言，支持从简单的状态转换到复杂的嵌套状态、并行状态、历史状态、超时处理等各种状态机模式，同时保持了良好的可扩展性和可维护性。

## 2. 1基本语法结构

```dsl
state_machine "order_state_machine" {
  description: "订单状态机"
  version: "1.0.0"
  author: "system"
  
  initial_state: "pending"
  final_states: ["completed", "cancelled", "refunded"]
  
  states: [
    {
      name: "pending"
      description: "待处理状态"
      entry_actions: ["notify_pending"]
      exit_actions: ["log_state_change"]
      allowed_events: ["confirm", "cancel"]
    },
    {
      name: "confirmed"
      description: "已确认状态"
      entry_actions: ["prepare_shipping"]
      exit_actions: ["log_state_change"]
      allowed_events: ["ship", "cancel"]
    },
    {
      name: "shipped"
      description: "已发货状态"
      entry_actions: ["start_delivery_tracking"]
      exit_actions: ["log_state_change"]
      allowed_events: ["deliver", "return"]
    },
    {
      name: "delivered"
      description: "已送达状态"
      entry_actions: ["start_completion_timer"]
      exit_actions: ["log_state_change"]
      allowed_events: ["complete", "return"]
    },
    {
      name: "completed"
      description: "已完成状态"
      entry_actions: ["finalize_order"]
      final: true
    },
    {
      name: "cancelled"
      description: "已取消状态"
      entry_actions: ["process_cancellation"]
      final: true
    },
    {
      name: "returned"
      description: "已退货状态"
      entry_actions: ["process_return_request"]
      allowed_events: ["refund"]
    },
    {
      name: "refunded"
      description: "已退款状态"
      entry_actions: ["finalize_refund"]
      final: true
    }
  ]
  
  transitions: [
    {
      from: "pending"
      to: "confirmed"
      event: "confirm"
      condition: "can_confirm_order(order_id)"
      actions: ["validate_order", "notify_confirmation"]
    },
    {
      from: "pending"
      to: "cancelled"
      event: "cancel"
      condition: "can_cancel_order(order_id)"
      actions: ["cancel_order", "notify_cancellation"]
    },
    {
      from: "confirmed"
      to: "shipped"
      event: "ship"
      condition: "inventory_available(order_id)"
      actions: ["prepare_shipment", "update_inventory"]
    },
    {
      from: "confirmed"
      to: "cancelled"
      event: "cancel"
      condition: "can_cancel_order(order_id)"
      actions: ["cancel_order", "restore_inventory"]
    },
    {
      from: "shipped"
      to: "delivered"
      event: "deliver"
      condition: "delivery_confirmed(order_id)"
      actions: ["complete_delivery", "notify_delivery"]
    },
    {
      from: "shipped"
      to: "returned"
      event: "return"
      condition: "return_requested(order_id)"
      actions: ["process_return", "notify_return"]
    },
    {
      from: "delivered"
      to: "completed"
      event: "complete"
      condition: "completion_confirmed(order_id)"
      actions: ["complete_order", "send_feedback_request"]
    },
    {
      from: "delivered"
      to: "returned"
      event: "return"
      condition: "return_requested(order_id)"
      actions: ["process_return", "notify_return"]
    },
    {
      from: "returned"
      to: "refunded"
      event: "refund"
      condition: "refund_processed(order_id)"
      actions: ["process_refund", "notify_refund"]
    }
  ]
  
  error_handling: {
    invalid_transition: {
      action: "log_error"
      message: "无效的状态转换"
    },
    condition_failed: {
      action: "notify_user"
      message: "操作条件不满足"
    },
    system_error: {
      action: "log_error_and_notify_admin"
      message: "系统错误"
    }
  }
  
  monitoring: {
    metrics: [
      "state_transition_count",
      "state_duration",
      "error_count"
    ],
    alerts: [
      {
        condition: "state_duration > 24h"
        action: "notify_admin"
        message: "状态停留时间过长"
      }
    ]
  }
}
```

## 3. 1关键元素

- state_machine：状态机声明
- description：描述信息
- version：版本号
- author：作者
- initial_state：初始状态
- final_states：最终状态列表
- states：状态定义
- transitions：状态转换定义
- error_handling：错误处理
- monitoring：监控配置

## 4. 1高级用法

### 4.1 1嵌套状态

```dsl
state_machine "complex_order_state_machine" {
  description: "复杂订单状态机"
  version: "1.0.0"
  
  initial_state: "processing"
  
  states: [
    {
      name: "processing"
      description: "处理中状态"
      composite: true
      states: [
        {
          name: "pending"
          description: "待处理"
          entry_actions: ["notify_pending"]
        },
        {
          name: "confirmed"
          description: "已确认"
          entry_actions: ["prepare_shipping"]
        }
      ]
      transitions: [
        {
          from: "pending"
          to: "confirmed"
          event: "confirm"
          condition: "can_confirm_order(order_id)"
        }
      ]
    },
    {
      name: "shipping"
      description: "配送中状态"
      composite: true
      states: [
        {
          name: "shipped"
          description: "已发货"
          entry_actions: ["start_delivery_tracking"]
        },
        {
          name: "in_transit"
          description: "运输中"
          entry_actions: ["update_tracking"]
        }
      ]
      transitions: [
        {
          from: "shipped"
          to: "in_transit"
          event: "start_transit"
        },
        {
          from: "in_transit"
          to: "delivered"
          event: "deliver"
          condition: "delivery_confirmed(order_id)"
        }
      ]
    },
    {
      name: "completed"
      description: "已完成状态"
      final: true
    }
  ]
  
  transitions: [
    {
      from: "processing"
      to: "shipping"
      event: "ship"
      condition: "inventory_available(order_id)"
    },
    {
      from: "shipping"
      to: "completed"
      event: "complete"
      condition: "completion_confirmed(order_id)"
    }
  ]
}
```

### 4.2 1并行状态

```dsl
state_machine "parallel_order_state_machine" {
  description: "并行订单状态机"
  version: "1.0.0"
  
  initial_state: "active"
  
  states: [
    {
      name: "active"
      description: "活跃状态"
      parallel: true
      regions: [
        {
          name: "payment_region"
          states: [
            {
              name: "unpaid"
              description: "未支付"
              transitions: [
                {
                  to: "paid"
                  event: "payment_success"
                }
              ]
            },
            {
              name: "paid"
              description: "已支付"
            }
          ]
        },
        {
          name: "inventory_region"
          states: [
            {
              name: "checking"
              description: "检查中"
              transitions: [
                {
                  to: "reserved"
                  event: "inventory_available"
                },
                {
                  to: "unavailable"
                  event: "inventory_unavailable"
                }
              ]
            },
            {
              name: "reserved"
              description: "已预留"
            },
            {
              name: "unavailable"
              description: "库存不足"
            }
          ]
        }
      ]
    },
    {
      name: "completed"
      description: "已完成状态"
      final: true
    }
  ]
  
  transitions: [
    {
      from: "active"
      to: "completed"
      event: "complete"
      condition: "all_regions_completed()"
    }
  ]
}
```

### 4.3 1历史状态

```dsl
state_machine "history_state_machine" {
  description: "历史状态机"
  version: "1.0.0"
  
  initial_state: "idle"
  
  states: [
    {
      name: "idle"
      description: "空闲状态"
      transitions: [
        {
          to: "working"
          event: "start_work"
        }
      ]
    },
    {
      name: "working"
      description: "工作状态"
      composite: true
      history: "deep"
      states: [
        {
          name: "processing"
          description: "处理中"
          transitions: [
            {
              to: "paused"
              event: "pause"
            },
            {
              to: "completed"
              event: "finish"
            }
          ]
        },
        {
          name: "paused"
          description: "暂停中"
          transitions: [
            {
              to: "processing"
              event: "resume"
            }
          ]
        },
        {
          name: "completed"
          description: "已完成"
        }
      ]
      transitions: [
        {
          to: "idle"
          event: "stop"
        }
      ]
    }
  ]
}
```

### 4.4 1超时处理

```dsl
state_machine "timeout_state_machine" {
  description: "超时状态机"
  version: "1.0.0"
  
  initial_state: "waiting"
  
  states: [
    {
      name: "waiting"
      description: "等待状态"
      timeout: {
        duration: "30s"
        action: "timeout_handler"
        target_state: "timeout"
      }
      transitions: [
        {
          to: "processing"
          event: "start"
        }
      ]
    },
    {
      name: "processing"
      description: "处理状态"
      timeout: {
        duration: "5m"
        action: "processing_timeout"
        target_state: "error"
      }
      transitions: [
        {
          to: "completed"
          event: "finish"
        }
      ]
    },
    {
      name: "completed"
      description: "已完成状态"
      final: true
    },
    {
      name: "timeout"
      description: "超时状态"
      final: true
    },
    {
      name: "error"
      description: "错误状态"
      final: true
    }
  ]
}
```

## 5. 1代码生成模板

### 5.1 1Java状态机生成

```java
// OrderStateMachine.java
public class OrderStateMachine {
    
    private OrderState currentState;
    private final OrderService orderService;
    private final NotificationService notificationService;
    
    public OrderStateMachine(OrderService orderService, NotificationService notificationService) {
        this.orderService = orderService;
        this.notificationService = notificationService;
        this.currentState = OrderState.PENDING;
    }
    
    public boolean transition(String event, int orderId) {
        try {
            switch (currentState) {
                case PENDING:
                    return handlePendingState(event, orderId);
                case CONFIRMED:
                    return handleConfirmedState(event, orderId);
                case SHIPPED:
                    return handleShippedState(event, orderId);
                case DELIVERED:
                    return handleDeliveredState(event, orderId);
                case RETURNED:
                    return handleReturnedState(event, orderId);
                default:
                    return false;
            }
        } catch (Exception e) {
            logError("状态转换失败", e);
            return false;
        }
    }
    
    private boolean handlePendingState(String event, int orderId) {
        switch (event) {
            case "confirm":
                if (canConfirmOrder(orderId)) {
                    validateOrder(orderId);
                    notifyConfirmation(orderId);
                    currentState = OrderState.CONFIRMED;
                    return true;
                }
                break;
            case "cancel":
                if (canCancelOrder(orderId)) {
                    cancelOrder(orderId);
                    notifyCancellation(orderId);
                    currentState = OrderState.CANCELLED;
                    return true;
                }
                break;
        }
        return false;
    }
    
    private boolean handleConfirmedState(String event, int orderId) {
        switch (event) {
            case "ship":
                if (inventoryAvailable(orderId)) {
                    prepareShipment(orderId);
                    updateInventory(orderId);
                    currentState = OrderState.SHIPPED;
                    return true;
                }
                break;
            case "cancel":
                if (canCancelOrder(orderId)) {
                    cancelOrder(orderId);
                    restoreInventory(orderId);
                    currentState = OrderState.CANCELLED;
                    return true;
                }
                break;
        }
        return false;
    }
    
    // 其他状态处理方法...
    
    private boolean canConfirmOrder(int orderId) {
        return orderService.canConfirmOrder(orderId);
    }
    
    private boolean canCancelOrder(int orderId) {
        return orderService.canCancelOrder(orderId);
    }
    
    private boolean inventoryAvailable(int orderId) {
        return orderService.inventoryAvailable(orderId);
    }
    
    private void validateOrder(int orderId) {
        orderService.validateOrder(orderId);
    }
    
    private void notifyConfirmation(int orderId) {
        notificationService.notifyConfirmation(orderId);
    }
    
    private void cancelOrder(int orderId) {
        orderService.cancelOrder(orderId);
    }
    
    private void notifyCancellation(int orderId) {
        notificationService.notifyCancellation(orderId);
    }
    
    private void prepareShipment(int orderId) {
        orderService.prepareShipment(orderId);
    }
    
    private void updateInventory(int orderId) {
        orderService.updateInventory(orderId);
    }
    
    private void restoreInventory(int orderId) {
        orderService.restoreInventory(orderId);
    }
    
    private void logError(String message, Exception e) {
        // 错误日志记录
    }
}
```

### 5.2 1Python状态机生成

```python
# order_state_machine.py
from enum import Enum
from typing import Dict, Any

class OrderState(Enum):
    PENDING = "pending"
    CONFIRMED = "confirmed"
    SHIPPED = "shipped"
    DELIVERED = "delivered"
    COMPLETED = "completed"
    CANCELLED = "cancelled"
    RETURNED = "returned"
    REFUNDED = "refunded"

class OrderStateMachine:
    
    def __init__(self, order_service, notification_service):
        self.current_state = OrderState.PENDING
        self.order_service = order_service
        self.notification_service = notification_service
        
        # 状态转换表
        self.transitions = {
            OrderState.PENDING: {
                'confirm': self._handle_confirm,
                'cancel': self._handle_cancel
            },
            OrderState.CONFIRMED: {
                'ship': self._handle_ship,
                'cancel': self._handle_cancel
            },
            OrderState.SHIPPED: {
                'deliver': self._handle_deliver,
                'return': self._handle_return
            },
            OrderState.DELIVERED: {
                'complete': self._handle_complete,
                'return': self._handle_return
            },
            OrderState.RETURNED: {
                'refund': self._handle_refund
            }
        }
    
    def transition(self, event: str, order_id: int) -> bool:
        try:
            if event in self.transitions.get(self.current_state, {}):
                handler = self.transitions[self.current_state][event]
                return handler(order_id)
            return False
        except Exception as e:
            self._log_error("状态转换失败", e)
            return False
    
    def _handle_confirm(self, order_id: int) -> bool:
        if self.order_service.can_confirm_order(order_id):
            self.order_service.validate_order(order_id)
            self.notification_service.notify_confirmation(order_id)
            self.current_state = OrderState.CONFIRMED
            return True
        return False
    
    def _handle_cancel(self, order_id: int) -> bool:
        if self.order_service.can_cancel_order(order_id):
            self.order_service.cancel_order(order_id)
            self.notification_service.notify_cancellation(order_id)
            self.current_state = OrderState.CANCELLED
            return True
        return False
    
    def _handle_ship(self, order_id: int) -> bool:
        if self.order_service.inventory_available(order_id):
            self.order_service.prepare_shipment(order_id)
            self.order_service.update_inventory(order_id)
            self.current_state = OrderState.SHIPPED
            return True
        return False
    
    def _handle_deliver(self, order_id: int) -> bool:
        if self.order_service.delivery_confirmed(order_id):
            self.order_service.complete_delivery(order_id)
            self.notification_service.notify_delivery(order_id)
            self.current_state = OrderState.DELIVERED
            return True
        return False
    
    def _handle_complete(self, order_id: int) -> bool:
        if self.order_service.completion_confirmed(order_id):
            self.order_service.complete_order(order_id)
            self.notification_service.send_feedback_request(order_id)
            self.current_state = OrderState.COMPLETED
            return True
        return False
    
    def _handle_return(self, order_id: int) -> bool:
        if self.order_service.return_requested(order_id):
            self.order_service.process_return(order_id)
            self.notification_service.notify_return(order_id)
            self.current_state = OrderState.RETURNED
            return True
        return False
    
    def _handle_refund(self, order_id: int) -> bool:
        if self.order_service.refund_processed(order_id):
            self.order_service.process_refund(order_id)
            self.notification_service.notify_refund(order_id)
            self.current_state = OrderState.REFUNDED
            return True
        return False
    
    def _log_error(self, message: str, error: Exception):
        # 错误日志记录
        pass
```

### 5.3 1JavaScript状态机生成

```javascript
// orderStateMachine.js
class OrderStateMachine {
    
    constructor(orderService, notificationService) {
        this.currentState = 'pending';
        this.orderService = orderService;
        this.notificationService = notificationService;
        
        // 状态转换表
        this.transitions = {
            pending: {
                confirm: this.handleConfirm.bind(this),
                cancel: this.handleCancel.bind(this)
            },
            confirmed: {
                ship: this.handleShip.bind(this),
                cancel: this.handleCancel.bind(this)
            },
            shipped: {
                deliver: this.handleDeliver.bind(this),
                return: this.handleReturn.bind(this)
            },
            delivered: {
                complete: this.handleComplete.bind(this),
                return: this.handleReturn.bind(this)
            },
            returned: {
                refund: this.handleRefund.bind(this)
            }
        };
    }
    
    transition(event, orderId) {
        try {
            if (this.transitions[this.currentState] && 
                this.transitions[this.currentState][event]) {
                const handler = this.transitions[this.currentState][event];
                return handler(orderId);
            }
            return false;
        } catch (error) {
            this.logError("状态转换失败", error);
            return false;
        }
    }
    
    async handleConfirm(orderId) {
        if (await this.orderService.canConfirmOrder(orderId)) {
            await this.orderService.validateOrder(orderId);
            await this.notificationService.notifyConfirmation(orderId);
            this.currentState = 'confirmed';
            return true;
        }
        return false;
    }
    
    async handleCancel(orderId) {
        if (await this.orderService.canCancelOrder(orderId)) {
            await this.orderService.cancelOrder(orderId);
            await this.notificationService.notifyCancellation(orderId);
            this.currentState = 'cancelled';
            return true;
        }
        return false;
    }
    
    async handleShip(orderId) {
        if (await this.orderService.inventoryAvailable(orderId)) {
            await this.orderService.prepareShipment(orderId);
            await this.orderService.updateInventory(orderId);
            this.currentState = 'shipped';
            return true;
        }
        return false;
    }
    
    async handleDeliver(orderId) {
        if (await this.orderService.deliveryConfirmed(orderId)) {
            await this.orderService.completeDelivery(orderId);
            await this.notificationService.notifyDelivery(orderId);
            this.currentState = 'delivered';
            return true;
        }
        return false;
    }
    
    async handleComplete(orderId) {
        if (await this.orderService.completionConfirmed(orderId)) {
            await this.orderService.completeOrder(orderId);
            await this.notificationService.sendFeedbackRequest(orderId);
            this.currentState = 'completed';
            return true;
        }
        return false;
    }
    
    async handleReturn(orderId) {
        if (await this.orderService.returnRequested(orderId)) {
            await this.orderService.processReturn(orderId);
            await this.notificationService.notifyReturn(orderId);
            this.currentState = 'returned';
            return true;
        }
        return false;
    }
    
    async handleRefund(orderId) {
        if (await this.orderService.refundProcessed(orderId)) {
            await this.orderService.processRefund(orderId);
            await this.notificationService.notifyRefund(orderId);
            this.currentState = 'refunded';
            return true;
        }
        return false;
    }
    
    logError(message, error) {
        // 错误日志记录
        console.error(message, error);
    }
}
```

## 6. 1验证规则

### 6.1 1语法验证规则

```yaml
validation:
  required_fields:
    - state_machine.name
    - state_machine.description
    - state_machine.version
    - state_machine.initial_state
    - state_machine.states
    - state_machine.transitions
  
  type_constraints:
    - field: "state_machine.name"
      type: "string"
      pattern: "^[a-zA-Z_][a-zA-Z0-9_]*$"
    - field: "state_machine.version"
      type: "string"
      pattern: "^[0-9]+\\.[0-9]+\\.[0-9]+$"
    - field: "state_machine.states"
      type: "array"
      min_items: 1
    - field: "state_machine.transitions"
      type: "array"
      min_items: 1
  
  business_rules:
    - rule: "state machine name must be unique"
    - rule: "initial state must exist in states"
    - rule: "final states must exist in states"
    - rule: "transition source and target states must exist"
```

### 6.2 1状态机验证规则

```yaml
state_machine_validation:
  state_consistency:
    - rule: "all states must have unique names"
    - rule: "final states must not have outgoing transitions"
    - rule: "initial state must not have incoming transitions"
  
  transition_validation:
    - rule: "all transitions must have valid source and target states"
    - rule: "transition conditions must be valid expressions"
    - rule: "transition actions must be valid function calls"
  
  error_handling:
    - rule: "all error scenarios must be handled"
    - rule: "error messages must be user-friendly"
    - rule: "timeout mechanisms must be defined for long-running states"
```

## 7. 1最佳实践

### 7.1 1状态机设计模式

```dsl
# 简单状态机模式
state_machine "simple_state_machine" {
  description: "简单状态机"
  
  initial_state: "start"
  final_states: ["end"]
  
  states: [
    {
      name: "start"
      description: "开始状态"
    },
    {
      name: "end"
      description: "结束状态"
      final: true
    }
  ]
  
  transitions: [
    {
      from: "start"
      to: "end"
      event: "finish"
    }
  ]
}

# 复杂状态机模式
state_machine "complex_state_machine" {
  description: "复杂状态机"
  
  initial_state: "idle"
  final_states: ["completed", "error"]
  
  states: [
    {
      name: "idle"
      description: "空闲状态"
      entry_actions: ["initialize"]
      exit_actions: ["cleanup"]
    },
    {
      name: "processing"
      description: "处理状态"
      composite: true
      states: [
        {
          name: "step1"
          description: "步骤1"
        },
        {
          name: "step2"
          description: "步骤2"
        }
      ]
    },
    {
      name: "completed"
      description: "已完成状态"
      final: true
    },
    {
      name: "error"
      description: "错误状态"
      final: true
    }
  ]
  
  transitions: [
    {
      from: "idle"
      to: "processing"
      event: "start"
      condition: "can_start()"
    },
    {
      from: "processing"
      to: "completed"
      event: "finish"
      condition: "all_steps_completed()"
    },
    {
      from: "*"
      to: "error"
      event: "error"
      condition: "has_error()"
    }
  ]
}
```

### 7.2 1状态机命名规范

```dsl
# 推荐命名模式
state_machine "entity_state_machine" {
  # 实体_状态机
}

state_machine "process_state_machine" {
  # 过程_状态机
}

state_machine "workflow_state_machine" {
  # 工作流_状态机
}
```

## 8. 1与主流标准的映射

| DSL元素 | UML State Machine | Spring Statemachine | XState | AWS Step Functions |
|---------|-------------------|---------------------|--------|-------------------|
| state_machine | state machine | state machine | machine | state machine |
| states | states | states | states | states |
| transitions | transitions | transitions | transitions | transitions |
| events | events | events | events | events |
| conditions | guards | guards | guards | conditions |
| actions | actions | actions | actions | actions |

## 9. 1工程实践示例

```dsl
# 电商订单状态机示例
state_machine "ecommerce_order_state_machine" {
  description: "电商订单状态机"
  version: "1.0.0"
  author: "system"
  
  initial_state: "pending"
  final_states: ["completed", "cancelled", "refunded"]
  
  states: [
    {
      name: "pending"
      description: "待处理状态"
      entry_actions: ["notify_pending"]
      exit_actions: ["log_state_change"]
      allowed_events: ["confirm", "cancel"]
      timeout: {
        duration: "24h"
        action: "auto_cancel"
        target_state: "cancelled"
      }
    },
    {
      name: "confirmed"
      description: "已确认状态"
      entry_actions: ["prepare_shipping"]
      exit_actions: ["log_state_change"]
      allowed_events: ["ship", "cancel"]
    },
    {
      name: "shipped"
      description: "已发货状态"
      entry_actions: ["start_delivery_tracking"]
      exit_actions: ["log_state_change"]
      allowed_events: ["deliver", "return"]
      timeout: {
        duration: "7d"
        action: "escalate_delivery"
        target_state: "shipped"
      }
    },
    {
      name: "delivered"
      description: "已送达状态"
      entry_actions: ["start_completion_timer"]
      exit_actions: ["log_state_change"]
      allowed_events: ["complete", "return"]
      timeout: {
        duration: "14d"
        action: "auto_complete"
        target_state: "completed"
      }
    },
    {
      name: "completed"
      description: "已完成状态"
      entry_actions: ["finalize_order"]
      final: true
    },
    {
      name: "cancelled"
      description: "已取消状态"
      entry_actions: ["process_cancellation"]
      final: true
    },
    {
      name: "returned"
      description: "已退货状态"
      entry_actions: ["process_return_request"]
      allowed_events: ["refund"]
    },
    {
      name: "refunded"
      description: "已退款状态"
      entry_actions: ["finalize_refund"]
      final: true
    }
  ]
  
  transitions: [
    {
      from: "pending"
      to: "confirmed"
      event: "confirm"
      condition: "can_confirm_order(order_id)"
      actions: ["validate_order", "notify_confirmation"]
    },
    {
      from: "pending"
      to: "cancelled"
      event: "cancel"
      condition: "can_cancel_order(order_id)"
      actions: ["cancel_order", "notify_cancellation"]
    },
    {
      from: "confirmed"
      to: "shipped"
      event: "ship"
      condition: "inventory_available(order_id)"
      actions: ["prepare_shipment", "update_inventory"]
    },
    {
      from: "confirmed"
      to: "cancelled"
      event: "cancel"
      condition: "can_cancel_order(order_id)"
      actions: ["cancel_order", "restore_inventory"]
    },
    {
      from: "shipped"
      to: "delivered"
      event: "deliver"
      condition: "delivery_confirmed(order_id)"
      actions: ["complete_delivery", "notify_delivery"]
    },
    {
      from: "shipped"
      to: "returned"
      event: "return"
      condition: "return_requested(order_id)"
      actions: ["process_return", "notify_return"]
    },
    {
      from: "delivered"
      to: "completed"
      event: "complete"
      condition: "completion_confirmed(order_id)"
      actions: ["complete_order", "send_feedback_request"]
    },
    {
      from: "delivered"
      to: "returned"
      event: "return"
      condition: "return_requested(order_id)"
      actions: ["process_return", "notify_return"]
    },
    {
      from: "returned"
      to: "refunded"
      event: "refund"
      condition: "refund_processed(order_id)"
      actions: ["process_refund", "notify_refund"]
    }
  ]
  
  error_handling: {
    invalid_transition: {
      action: "log_error"
      message: "无效的状态转换"
    },
    condition_failed: {
      action: "notify_user"
      message: "操作条件不满足"
    },
    system_error: {
      action: "log_error_and_notify_admin"
      message: "系统错误"
    }
  }
  
  monitoring: {
    metrics: [
      "state_transition_count",
      "state_duration",
      "error_count",
      "timeout_count"
    ],
    alerts: [
      {
        condition: "state_duration > 24h"
        action: "notify_admin"
        message: "状态停留时间过长"
      },
      {
        condition: "error_count > 10"
        action: "notify_admin"
        message: "状态机错误次数过多"
      }
    ]
  }
}
```

这个DSL设计为状态机建模提供了完整的配置语言，支持从简单的状态转换到复杂的嵌套状态、并行状态、历史状态、超时处理等各种状态机模式，同时保持了良好的可扩展性和可维护性。
