# 工作流建模DSL草案

## 1. 设计目标

- 用统一DSL描述业务流程、任务编排、状态管理、条件分支等要素
- 支持自动生成工作流引擎配置、流程编排脚本、状态机代码等
- 支持并行执行、条件分支、异常处理、监控告警等高级特性

## 2. 基本语法结构

```dsl
workflow "order_processing_workflow" {
  description: "订单处理工作流"
  version: "1.0.0"
  author: "system"
  
  inputs: [
    { name: "order_id", type: "int", required: true },
    { name: "user_id", type: "int", required: true },
    { name: "items", type: "array<OrderItem>", required: true }
  ]
  
  outputs: [
    { name: "order_status", type: "string" },
    { name: "processing_result", type: "object" }
  ]
  
  variables: [
    { name: "total_amount", type: "decimal" },
    { name: "payment_status", type: "string" },
    { name: "inventory_status", type: "string" }
  ]
  
  steps: [
    {
      name: "validate_order"
      type: "task"
      action: "validate_order_data"
      inputs: ["order_id", "user_id", "items"]
      outputs: ["validation_result"]
      timeout: "30s"
      retry: {
        max_attempts: 3
        backoff: "exponential"
        initial_delay: "5s"
      }
    },
    {
      name: "check_inventory"
      type: "task"
      action: "check_inventory_availability"
      inputs: ["items"]
      outputs: ["inventory_status"]
      condition: "validation_result.success == true"
    },
    {
      name: "calculate_total"
      type: "task"
      action: "calculate_order_total"
      inputs: ["items"]
      outputs: ["total_amount"]
      condition: "inventory_status.available == true"
    },
    {
      name: "process_payment"
      type: "task"
      action: "process_payment"
      inputs: ["total_amount", "user_id"]
      outputs: ["payment_status"]
      condition: "total_amount > 0"
    },
    {
      name: "update_inventory"
      type: "task"
      action: "update_inventory_levels"
      inputs: ["items"]
      condition: "payment_status.success == true"
    },
    {
      name: "send_confirmation"
      type: "task"
      action: "send_order_confirmation"
      inputs: ["user_id", "order_id"]
      async: true
      condition: "payment_status.success == true"
    }
  ]
  
  error_handling: {
    validation_error: {
      action: "return_error"
      message: "订单验证失败"
    },
    inventory_error: {
      action: "notify_user"
      message: "库存不足，订单无法处理"
    },
    payment_error: {
      action: "rollback_inventory"
      message: "支付失败，已回滚库存"
    },
    system_error: {
      action: "log_error_and_notify_admin"
      message: "系统错误，请联系管理员"
    }
  }
  
  monitoring: {
    metrics: [
      "workflow_duration",
      "step_success_rate",
      "error_count"
    ],
    alerts: [
      {
        condition: "workflow_duration > 300s"
        action: "notify_admin"
        message: "工作流执行时间过长"
      },
      {
        condition: "error_count > 5"
        action: "notify_admin"
        message: "工作流错误次数过多"
      }
    ]
  }
}
```

## 3. 关键元素

- workflow：工作流声明
- description：描述信息
- version：版本号
- author：作者
- inputs：输入参数
- outputs：输出参数
- variables：工作流变量
- steps：工作流步骤
- error_handling：错误处理
- monitoring：监控配置

## 4. 高级用法

### 4.1 并行执行与条件分支

```dsl
workflow "complex_order_processing" {
  description: "复杂订单处理工作流"
  version: "1.0.0"
  
  inputs: [
    { name: "order_id", type: "int", required: true },
    { name: "user_id", type: "int", required: true },
    { name: "items", type: "array<OrderItem>", required: true }
  ]
  
  outputs: [
    { name: "order_status", type: "string" },
    { name: "processing_result", type: "object" }
  ]
  
  variables: [
    { name: "total_amount", type: "decimal" },
    { name: "discount_amount", type: "decimal" },
    { name: "final_amount", type: "decimal" }
  ]
  
  steps: [
    {
      name: "validate_order"
      type: "task"
      action: "validate_order_data"
      inputs: ["order_id", "user_id", "items"]
      outputs: ["validation_result"]
    },
    {
      name: "parallel_processing"
      type: "parallel"
      branches: [
        {
          name: "inventory_check"
          steps: [
            {
              name: "check_inventory"
              type: "task"
              action: "check_inventory_availability"
              inputs: ["items"]
              outputs: ["inventory_status"]
            }
          ]
        },
        {
          name: "user_analysis"
          steps: [
            {
              name: "analyze_user"
              type: "task"
              action: "analyze_user_behavior"
              inputs: ["user_id"]
              outputs: ["user_analysis"]
            },
            {
              name: "calculate_discount"
              type: "task"
              action: "calculate_user_discount"
              inputs: ["user_analysis"]
              outputs: ["discount_amount"]
            }
          ]
        }
      ]
      condition: "validation_result.success == true"
    },
    {
      name: "conditional_processing"
      type: "conditional"
      condition: "inventory_status.available == true AND discount_amount > 0"
      true_branch: [
        {
          name: "apply_discount"
          type: "task"
          action: "apply_discount_to_order"
          inputs: ["discount_amount"]
          outputs: ["final_amount"]
        }
      ],
      false_branch: [
        {
          name: "use_original_amount"
          type: "task"
          action: "set_final_amount"
          inputs: ["total_amount"]
          outputs: ["final_amount"]
        }
      ]
    },
    {
      name: "process_payment"
      type: "task"
      action: "process_payment"
      inputs: ["final_amount", "user_id"]
      outputs: ["payment_status"]
      condition: "final_amount > 0"
    }
  ]
  
  error_handling: {
    validation_error: {
      action: "return_error"
      message: "订单验证失败"
    },
    inventory_error: {
      action: "notify_user"
      message: "库存不足"
    },
    payment_error: {
      action: "rollback_and_notify"
      message: "支付失败"
    }
  }
}
```

### 4.2 状态机与状态转换

```dsl
workflow "order_state_machine" {
  description: "订单状态机工作流"
  version: "1.0.0"
  
  inputs: [
    { name: "order_id", type: "int", required: true },
    { name: "action", type: "string", required: true }
  ]
  
  outputs: [
    { name: "new_state", type: "string" },
    { name: "state_changed", type: "boolean" }
  ]
  
  state_machine: {
    initial_state: "pending"
    states: [
      {
        name: "pending"
        allowed_actions: ["confirm", "cancel"]
        entry_actions: ["notify_pending"]
        exit_actions: ["log_state_change"]
        transitions: [
          {
            action: "confirm"
            target: "confirmed"
            condition: "can_confirm_order(order_id)"
            actions: ["validate_order", "notify_confirmation"]
          },
          {
            action: "cancel"
            target: "cancelled"
            condition: "can_cancel_order(order_id)"
            actions: ["cancel_order", "notify_cancellation"]
          }
        ]
      },
      {
        name: "confirmed"
        allowed_actions: ["ship", "cancel"]
        entry_actions: ["prepare_shipping"]
        transitions: [
          {
            action: "ship"
            target: "shipped"
            condition: "inventory_available(order_id)"
            actions: ["prepare_shipment", "update_inventory"]
          },
          {
            action: "cancel"
            target: "cancelled"
            condition: "can_cancel_order(order_id)"
            actions: ["cancel_order", "restore_inventory"]
          }
        ]
      },
      {
        name: "shipped"
        allowed_actions: ["deliver", "return"]
        entry_actions: ["start_delivery_tracking"]
        transitions: [
          {
            action: "deliver"
            target: "delivered"
            condition: "delivery_confirmed(order_id)"
            actions: ["complete_delivery", "notify_delivery"]
          },
          {
            action: "return"
            target: "returned"
            condition: "return_requested(order_id)"
            actions: ["process_return", "notify_return"]
          }
        ]
      },
      {
        name: "delivered"
        allowed_actions: ["complete", "return"]
        entry_actions: ["start_completion_timer"]
        transitions: [
          {
            action: "complete"
            target: "completed"
            condition: "completion_confirmed(order_id)"
            actions: ["complete_order", "send_feedback_request"]
          },
          {
            action: "return"
            target: "returned"
            condition: "return_requested(order_id)"
            actions: ["process_return", "notify_return"]
          }
        ]
      },
      {
        name: "cancelled"
        allowed_actions: []
        entry_actions: ["process_cancellation"]
        final: true
      },
      {
        name: "returned"
        allowed_actions: ["refund"]
        entry_actions: ["process_return_request"]
        transitions: [
          {
            action: "refund"
            target: "refunded"
            condition: "refund_processed(order_id)"
            actions: ["process_refund", "notify_refund"]
          }
        ]
      },
      {
        name: "completed"
        allowed_actions: []
        entry_actions: ["finalize_order"]
        final: true
      },
      {
        name: "refunded"
        allowed_actions: []
        entry_actions: ["finalize_refund"]
        final: true
      }
    ]
  }
  
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
}
```

### 4.3 循环与迭代处理

```dsl
workflow "batch_processing_workflow" {
  description: "批量处理工作流"
  version: "1.0.0"
  
  inputs: [
    { name: "batch_id", type: "int", required: true },
    { name: "items", type: "array<ProcessingItem>", required: true }
  ]
  
  outputs: [
    { name: "processing_results", type: "array<ProcessingResult>" },
    { name: "success_count", type: "int" },
    { name: "failure_count", type: "int" }
  ]
  
  variables: [
    { name: "current_index", type: "int", initial: 0 },
    { name: "results", type: "array<ProcessingResult>", initial: [] },
    { name: "success_count", type: "int", initial: 0 },
    { name: "failure_count", type: "int", initial: 0 }
  ]
  
  steps: [
    {
      name: "initialize_batch"
      type: "task"
      action: "initialize_batch_processing"
      inputs: ["batch_id"]
      outputs: ["batch_status"]
    },
    {
      name: "process_items_loop"
      type: "loop"
      condition: "current_index < items.length"
      steps: [
        {
          name: "process_current_item"
          type: "task"
          action: "process_single_item"
          inputs: ["items[current_index]"]
          outputs: ["processing_result"]
        },
        {
          name: "update_results"
          type: "task"
          action: "update_processing_results"
          inputs: ["processing_result"]
          outputs: ["results", "success_count", "failure_count"]
        },
        {
          name: "increment_index"
          type: "task"
          action: "increment_current_index"
          inputs: ["current_index"]
          outputs: ["current_index"]
        }
      ]
    },
    {
      name: "finalize_batch"
      type: "task"
      action: "finalize_batch_processing"
      inputs: ["batch_id", "results", "success_count", "failure_count"]
      outputs: ["final_results"]
    }
  ]
  
  error_handling: {
    item_processing_error: {
      action: "continue_with_next_item"
      message: "单个项目处理失败，继续处理下一个"
    },
    batch_error: {
      action: "rollback_batch"
      message: "批量处理失败，回滚所有操作"
    }
  }
}
```

### 4.4 事件驱动工作流

```dsl
workflow "event_driven_order_workflow" {
  description: "事件驱动订单工作流"
  version: "1.0.0"
  
  inputs: [
    { name: "order_id", type: "int", required: true }
  ]
  
  outputs: [
    { name: "workflow_status", type: "string" }
  ]
  
  events: [
    {
      name: "order_created"
      source: "order_service"
      payload: {
        order_id: "int",
        user_id: "int",
        items: "array<OrderItem>"
      }
    },
    {
      name: "payment_processed"
      source: "payment_service"
      payload: {
        order_id: "int",
        payment_status: "string",
        amount: "decimal"
      }
    },
    {
      name: "inventory_updated"
      source: "inventory_service"
      payload: {
        order_id: "int",
        inventory_status: "string"
      }
    },
    {
      name: "shipping_started"
      source: "shipping_service"
      payload: {
        order_id: "int",
        tracking_number: "string"
      }
    }
  ]
  
  event_handlers: [
    {
      event: "order_created"
      actions: [
        {
          name: "validate_order"
          type: "task"
          action: "validate_order_data"
          inputs: ["order_id", "user_id", "items"]
          outputs: ["validation_result"]
        },
        {
          name: "trigger_parallel_checks"
          type: "parallel"
          branches: [
            {
              name: "inventory_check"
              steps: [
                {
                  name: "check_inventory"
                  type: "task"
                  action: "check_inventory_availability"
                  inputs: ["items"]
                  outputs: ["inventory_status"]
                }
              ]
            },
            {
              name: "payment_preparation"
              steps: [
                {
                  name: "prepare_payment"
                  type: "task"
                  action: "prepare_payment_processing"
                  inputs: ["order_id", "user_id"]
                  outputs: ["payment_preparation"]
                }
              ]
            }
          ]
        }
      ]
    },
    {
      event: "payment_processed"
      condition: "payment_status == 'success'"
      actions: [
        {
          name: "update_order_status"
          type: "task"
          action: "update_order_to_paid"
          inputs: ["order_id"]
          outputs: ["order_status"]
        },
        {
          name: "trigger_shipping"
          type: "task"
          action: "initiate_shipping_process"
          inputs: ["order_id"]
          outputs: ["shipping_initiated"]
        }
      ]
    },
    {
      event: "inventory_updated"
      condition: "inventory_status == 'reserved'"
      actions: [
        {
          name: "confirm_inventory"
          type: "task"
          action: "confirm_inventory_reservation"
          inputs: ["order_id"]
          outputs: ["inventory_confirmed"]
        }
      ]
    },
    {
      event: "shipping_started"
      actions: [
        {
          name: "update_tracking"
          type: "task"
          action: "update_order_tracking"
          inputs: ["order_id", "tracking_number"]
          outputs: ["tracking_updated"]
        },
        {
          name: "notify_customer"
          type: "task"
          action: "notify_customer_shipping"
          inputs: ["order_id", "tracking_number"]
          async: true
        }
      ]
    }
  ]
  
  timeout: {
    duration: "24h"
    action: "escalate_to_admin"
    message: "工作流执行超时"
  }
  
  error_handling: {
    event_processing_error: {
      action: "retry_with_backoff"
      max_retries: 3
      backoff: "exponential"
    },
    workflow_timeout: {
      action: "notify_admin"
      message: "工作流执行超时"
    }
  }
}
```

## 5. 代码生成模板

### 5.1 Java工作流生成

```java
// OrderProcessingWorkflow.java
public class OrderProcessingWorkflow {
    
    private final WorkflowEngine workflowEngine;
    private final OrderService orderService;
    private final InventoryService inventoryService;
    private final PaymentService paymentService;
    
    public OrderProcessingWorkflow(WorkflowEngine workflowEngine,
                                 OrderService orderService,
                                 InventoryService inventoryService,
                                 PaymentService paymentService) {
        this.workflowEngine = workflowEngine;
        this.orderService = orderService;
        this.inventoryService = inventoryService;
        this.paymentService = paymentService;
    }
    
    public WorkflowResult execute(OrderProcessingInput input) {
        WorkflowContext context = new WorkflowContext();
        context.setInput(input);
        
        try {
            // Step 1: Validate Order
            ValidationResult validationResult = validateOrder(input);
            if (!validationResult.isSuccess()) {
                return WorkflowResult.error("订单验证失败: " + validationResult.getMessage());
            }
            context.setVariable("validation_result", validationResult);
            
            // Step 2: Check Inventory
            InventoryStatus inventoryStatus = checkInventory(input.getItems());
            context.setVariable("inventory_status", inventoryStatus);
            
            if (!inventoryStatus.isAvailable()) {
                return WorkflowResult.error("库存不足");
            }
            
            // Step 3: Calculate Total
            BigDecimal totalAmount = calculateOrderTotal(input.getItems());
            context.setVariable("total_amount", totalAmount);
            
            // Step 4: Process Payment
            PaymentStatus paymentStatus = processPayment(totalAmount, input.getUserId());
            context.setVariable("payment_status", paymentStatus);
            
            if (!paymentStatus.isSuccess()) {
                return WorkflowResult.error("支付失败: " + paymentStatus.getMessage());
            }
            
            // Step 5: Update Inventory
            updateInventory(input.getItems());
            
            // Step 6: Send Confirmation (async)
            CompletableFuture.runAsync(() -> 
                sendOrderConfirmation(input.getUserId(), input.getOrderId())
            );
            
            return WorkflowResult.success("订单处理成功");
            
        } catch (Exception e) {
            return WorkflowResult.error("系统错误: " + e.getMessage());
        }
    }
    
    private ValidationResult validateOrder(OrderProcessingInput input) {
        return orderService.validateOrder(input.getOrderId(), input.getUserId(), input.getItems());
    }
    
    private InventoryStatus checkInventory(List<OrderItem> items) {
        return inventoryService.checkAvailability(items);
    }
    
    private BigDecimal calculateOrderTotal(List<OrderItem> items) {
        return items.stream()
                   .map(item -> item.getPrice().multiply(BigDecimal.valueOf(item.getQuantity())))
                   .reduce(BigDecimal.ZERO, BigDecimal::add);
    }
    
    private PaymentStatus processPayment(BigDecimal amount, int userId) {
        return paymentService.processPayment(amount, userId);
    }
    
    private void updateInventory(List<OrderItem> items) {
        inventoryService.updateLevels(items);
    }
    
    private void sendOrderConfirmation(int userId, int orderId) {
        // Async notification logic
    }
}
```

### 5.2 Python工作流生成

```python
# order_processing_workflow.py
import asyncio
from typing import List, Dict, Any
from decimal import Decimal

class OrderProcessingWorkflow:
    
    def __init__(self, order_service, inventory_service, payment_service):
        self.order_service = order_service
        self.inventory_service = inventory_service
        self.payment_service = payment_service
    
    async def execute(self, order_id: int, user_id: int, items: List[Dict]) -> Dict[str, Any]:
        context = {
            'order_id': order_id,
            'user_id': user_id,
            'items': items,
            'variables': {}
        }
        
        try:
            # Step 1: Validate Order
            validation_result = await self.validate_order(order_id, user_id, items)
            if not validation_result['success']:
                return {'status': 'error', 'message': f"订单验证失败: {validation_result['message']}"}
            
            context['variables']['validation_result'] = validation_result
            
            # Step 2: Check Inventory
            inventory_status = await self.check_inventory(items)
            context['variables']['inventory_status'] = inventory_status
            
            if not inventory_status['available']:
                return {'status': 'error', 'message': '库存不足'}
            
            # Step 3: Calculate Total
            total_amount = self.calculate_order_total(items)
            context['variables']['total_amount'] = total_amount
            
            # Step 4: Process Payment
            payment_status = await self.process_payment(total_amount, user_id)
            context['variables']['payment_status'] = payment_status
            
            if not payment_status['success']:
                return {'status': 'error', 'message': f"支付失败: {payment_status['message']}"}
            
            # Step 5: Update Inventory
            await self.update_inventory(items)
            
            # Step 6: Send Confirmation (async)
            asyncio.create_task(self.send_order_confirmation(user_id, order_id))
            
            return {
                'status': 'success',
                'message': '订单处理成功',
                'order_status': 'confirmed',
                'processing_result': {
                    'total_amount': total_amount,
                    'payment_status': payment_status['status']
                }
            }
            
        except Exception as e:
            return {'status': 'error', 'message': f"系统错误: {str(e)}"}
    
    async def validate_order(self, order_id: int, user_id: int, items: List[Dict]) -> Dict[str, Any]:
        return await self.order_service.validate_order(order_id, user_id, items)
    
    async def check_inventory(self, items: List[Dict]) -> Dict[str, Any]:
        return await self.inventory_service.check_availability(items)
    
    def calculate_order_total(self, items: List[Dict]) -> Decimal:
        total = Decimal('0')
        for item in items:
            total += Decimal(str(item['price'])) * Decimal(str(item['quantity']))
        return total
    
    async def process_payment(self, amount: Decimal, user_id: int) -> Dict[str, Any]:
        return await self.payment_service.process_payment(amount, user_id)
    
    async def update_inventory(self, items: List[Dict]):
        await self.inventory_service.update_levels(items)
    
    async def send_order_confirmation(self, user_id: int, order_id: int):
        # Async notification logic
        pass
```

### 5.3 JavaScript工作流生成

```javascript
// orderProcessingWorkflow.js
class OrderProcessingWorkflow {
    
    constructor(orderService, inventoryService, paymentService) {
        this.orderService = orderService;
        this.inventoryService = inventoryService;
        this.paymentService = paymentService;
    }
    
    async execute(orderId, userId, items) {
        const context = {
            orderId,
            userId,
            items,
            variables: {}
        };
        
        try {
            // Step 1: Validate Order
            const validationResult = await this.validateOrder(orderId, userId, items);
            if (!validationResult.success) {
                return {
                    status: 'error',
                    message: `订单验证失败: ${validationResult.message}`
                };
            }
            context.variables.validationResult = validationResult;
            
            // Step 2: Check Inventory
            const inventoryStatus = await this.checkInventory(items);
            context.variables.inventoryStatus = inventoryStatus;
            
            if (!inventoryStatus.available) {
                return {
                    status: 'error',
                    message: '库存不足'
                };
            }
            
            // Step 3: Calculate Total
            const totalAmount = this.calculateOrderTotal(items);
            context.variables.totalAmount = totalAmount;
            
            // Step 4: Process Payment
            const paymentStatus = await this.processPayment(totalAmount, userId);
            context.variables.paymentStatus = paymentStatus;
            
            if (!paymentStatus.success) {
                return {
                    status: 'error',
                    message: `支付失败: ${paymentStatus.message}`
                };
            }
            
            // Step 5: Update Inventory
            await this.updateInventory(items);
            
            // Step 6: Send Confirmation (async)
            setImmediate(() => this.sendOrderConfirmation(userId, orderId));
            
            return {
                status: 'success',
                message: '订单处理成功',
                orderStatus: 'confirmed',
                processingResult: {
                    totalAmount,
                    paymentStatus: paymentStatus.status
                }
            };
            
        } catch (error) {
            return {
                status: 'error',
                message: `系统错误: ${error.message}`
            };
        }
    }
    
    async validateOrder(orderId, userId, items) {
        return await this.orderService.validateOrder(orderId, userId, items);
    }
    
    async checkInventory(items) {
        return await this.inventoryService.checkAvailability(items);
    }
    
    calculateOrderTotal(items) {
        return items.reduce((total, item) => {
            return total + (item.price * item.quantity);
        }, 0);
    }
    
    async processPayment(amount, userId) {
        return await this.paymentService.processPayment(amount, userId);
    }
    
    async updateInventory(items) {
        await this.inventoryService.updateLevels(items);
    }
    
    async sendOrderConfirmation(userId, orderId) {
        // Async notification logic
    }
}
```

## 6. 验证规则

### 6.1 语法验证规则

```yaml
validation:
  required_fields:
    - workflow.name
    - workflow.description
    - workflow.version
    - workflow.steps
  
  type_constraints:
    - field: "workflow.name"
      type: "string"
      pattern: "^[a-zA-Z_][a-zA-Z0-9_]*$"
    - field: "workflow.version"
      type: "string"
      pattern: "^[0-9]+\\.[0-9]+\\.[0-9]+$"
    - field: "workflow.steps"
      type: "array"
      min_items: 1
  
  business_rules:
    - rule: "workflow name must be unique"
    - rule: "all input parameters must be used in steps"
    - rule: "all output parameters must be set in steps"
    - rule: "step names must be unique within workflow"
```

### 6.2 工作流验证规则

```yaml
workflow_validation:
  step_consistency:
    - rule: "steps must be in logical order"
    - rule: "all required inputs must be available before use"
    - rule: "output parameters must be set before return"
  
  state_machine_validation:
    - rule: "state machine must have valid initial state"
    - rule: "all states must have valid transitions"
    - rule: "final states must not have outgoing transitions"
  
  error_handling:
    - rule: "all error scenarios must be handled"
    - rule: "error messages must be user-friendly"
    - rule: "timeout mechanisms must be defined for long-running workflows"
```

## 7. 最佳实践

### 7.1 工作流设计模式

```dsl
# 线性处理模式
workflow "linear_processing" {
  description: "线性处理工作流"
  
  inputs: [
    { name: "data", type: "object", required: true }
  ]
  
  outputs: [
    { name: "result", type: "object" }
  ]
  
  steps: [
    {
      name: "step1"
      type: "task"
      action: "process_step1"
      inputs: ["data"]
      outputs: ["step1_result"]
    },
    {
      name: "step2"
      type: "task"
      action: "process_step2"
      inputs: ["step1_result"]
      outputs: ["step2_result"]
    },
    {
      name: "step3"
      type: "task"
      action: "process_step3"
      inputs: ["step2_result"]
      outputs: ["result"]
    }
  ]
}

# 并行处理模式
workflow "parallel_processing" {
  description: "并行处理工作流"
  
  inputs: [
    { name: "data", type: "object", required: true }
  ]
  
  outputs: [
    { name: "result", type: "object" }
  ]
  
  steps: [
    {
      name: "parallel_tasks"
      type: "parallel"
      branches: [
        {
          name: "branch1"
          steps: [
            {
              name: "task1"
              type: "task"
              action: "process_task1"
              inputs: ["data"]
              outputs: ["task1_result"]
            }
          ]
        },
        {
          name: "branch2"
          steps: [
            {
              name: "task2"
              type: "task"
              action: "process_task2"
              inputs: ["data"]
              outputs: ["task2_result"]
            }
          ]
        }
      ]
    },
    {
      name: "combine_results"
      type: "task"
      action: "combine_parallel_results"
      inputs: ["task1_result", "task2_result"]
      outputs: ["result"]
    }
  ]
}
```

### 7.2 工作流命名规范

```dsl
# 推荐命名模式
workflow "entity_action_workflow" {
  # 实体_操作_工作流
}

workflow "process_entity_workflow" {
  # 处理_实体_工作流
}

workflow "entity_state_machine" {
  # 实体_状态机
}
```

## 8. 与主流标准的映射

| DSL元素 | Apache Airflow | Temporal | Camunda | AWS Step Functions |
|---------|----------------|----------|---------|-------------------|
| workflow | dag | workflow | process | state machine |
| steps | tasks | activities | tasks | states |
| parallel | parallel | parallel | parallel gateway | parallel |
| conditional | branching | conditional | exclusive gateway | choice |
| loop | loop | loop | loop | map |
| error_handling | error handling | error handling | error handling | catch |

## 9. 工程实践示例

```dsl
# 电商系统工作流示例
workflow "ecommerce_order_workflow" {
  description: "电商订单处理工作流"
  version: "1.0.0"
  author: "system"
  
  inputs: [
    { name: "order_id", type: "int", required: true },
    { name: "user_id", type: "int", required: true },
    { name: "items", type: "array<OrderItem>", required: true }
  ]
  
  outputs: [
    { name: "order_status", type: "string" },
    { name: "processing_result", type: "object" }
  ]
  
  variables: [
    { name: "total_amount", type: "decimal" },
    { name: "discount_amount", type: "decimal" },
    { name: "final_amount", type: "decimal" }
  ]
  
  steps: [
    {
      name: "validate_order"
      type: "task"
      action: "validate_order_data"
      inputs: ["order_id", "user_id", "items"]
      outputs: ["validation_result"]
      timeout: "30s"
      retry: {
        max_attempts: 3
        backoff: "exponential"
        initial_delay: "5s"
      }
    },
    {
      name: "parallel_checks"
      type: "parallel"
      branches: [
        {
          name: "inventory_check"
          steps: [
            {
              name: "check_inventory"
              type: "task"
              action: "check_inventory_availability"
              inputs: ["items"]
              outputs: ["inventory_status"]
            }
          ]
        },
        {
          name: "user_analysis"
          steps: [
            {
              name: "analyze_user"
              type: "task"
              action: "analyze_user_behavior"
              inputs: ["user_id"]
              outputs: ["user_analysis"]
            },
            {
              name: "calculate_discount"
              type: "task"
              action: "calculate_user_discount"
              inputs: ["user_analysis"]
              outputs: ["discount_amount"]
            }
          ]
        }
      ]
      condition: "validation_result.success == true"
    },
    {
      name: "calculate_total"
      type: "task"
      action: "calculate_order_total"
      inputs: ["items"]
      outputs: ["total_amount"]
      condition: "inventory_status.available == true"
    },
    {
      name: "apply_discount"
      type: "task"
      action: "apply_discount_to_order"
      inputs: ["total_amount", "discount_amount"]
      outputs: ["final_amount"]
      condition: "discount_amount > 0"
    },
    {
      name: "process_payment"
      type: "task"
      action: "process_payment"
      inputs: ["final_amount", "user_id"]
      outputs: ["payment_status"]
      condition: "final_amount > 0"
    },
    {
      name: "update_inventory"
      type: "task"
      action: "update_inventory_levels"
      inputs: ["items"]
      condition: "payment_status.success == true"
    },
    {
      name: "send_notifications"
      type: "parallel"
      branches: [
        {
          name: "customer_notification"
          steps: [
            {
              name: "send_order_confirmation"
              type: "task"
              action: "send_order_confirmation"
              inputs: ["user_id", "order_id"]
              async: true
            }
          ]
        },
        {
          name: "admin_notification"
          steps: [
            {
              name: "notify_admin"
              type: "task"
              action: "notify_admin_new_order"
              inputs: ["order_id", "final_amount"]
              async: true
            }
          ]
        }
      ]
      condition: "payment_status.success == true"
    }
  ]
  
  error_handling: {
    validation_error: {
      action: "return_error"
      message: "订单验证失败"
    },
    inventory_error: {
      action: "notify_user"
      message: "库存不足，订单无法处理"
    },
    payment_error: {
      action: "rollback_inventory"
      message: "支付失败，已回滚库存"
    },
    system_error: {
      action: "log_error_and_notify_admin"
      message: "系统错误，请联系管理员"
    }
  }
  
  monitoring: {
    metrics: [
      "workflow_duration",
      "step_success_rate",
      "error_count",
      "payment_success_rate"
    ],
    alerts: [
      {
        condition: "workflow_duration > 300s"
        action: "notify_admin"
        message: "工作流执行时间过长"
      },
      {
        condition: "payment_success_rate < 0.95"
        action: "notify_admin"
        message: "支付成功率过低"
      }
    ]
  }
}
```

这个DSL设计为工作流建模提供了完整的配置语言，支持从简单的线性流程到复杂的并行处理、状态机、事件驱动等各种工作流模式，同时保持了良好的可扩展性和可维护性。

## 2. 1基本语法结构

```dsl
workflow "order_processing_workflow" {
  description: "订单处理工作流"
  version: "1.0.0"
  author: "system"
  
  inputs: [
    { name: "order_id", type: "int", required: true },
    { name: "user_id", type: "int", required: true },
    { name: "items", type: "array<OrderItem>", required: true }
  ]
  
  outputs: [
    { name: "order_status", type: "string" },
    { name: "processing_result", type: "object" }
  ]
  
  variables: [
    { name: "total_amount", type: "decimal" },
    { name: "payment_status", type: "string" },
    { name: "inventory_status", type: "string" }
  ]
  
  steps: [
    {
      name: "validate_order"
      type: "task"
      action: "validate_order_data"
      inputs: ["order_id", "user_id", "items"]
      outputs: ["validation_result"]
      timeout: "30s"
      retry: {
        max_attempts: 3
        backoff: "exponential"
        initial_delay: "5s"
      }
    },
    {
      name: "check_inventory"
      type: "task"
      action: "check_inventory_availability"
      inputs: ["items"]
      outputs: ["inventory_status"]
      condition: "validation_result.success == true"
    },
    {
      name: "calculate_total"
      type: "task"
      action: "calculate_order_total"
      inputs: ["items"]
      outputs: ["total_amount"]
      condition: "inventory_status.available == true"
    },
    {
      name: "process_payment"
      type: "task"
      action: "process_payment"
      inputs: ["total_amount", "user_id"]
      outputs: ["payment_status"]
      condition: "total_amount > 0"
    },
    {
      name: "update_inventory"
      type: "task"
      action: "update_inventory_levels"
      inputs: ["items"]
      condition: "payment_status.success == true"
    },
    {
      name: "send_confirmation"
      type: "task"
      action: "send_order_confirmation"
      inputs: ["user_id", "order_id"]
      async: true
      condition: "payment_status.success == true"
    }
  ]
  
  error_handling: {
    validation_error: {
      action: "return_error"
      message: "订单验证失败"
    },
    inventory_error: {
      action: "notify_user"
      message: "库存不足，订单无法处理"
    },
    payment_error: {
      action: "rollback_inventory"
      message: "支付失败，已回滚库存"
    },
    system_error: {
      action: "log_error_and_notify_admin"
      message: "系统错误，请联系管理员"
    }
  }
  
  monitoring: {
    metrics: [
      "workflow_duration",
      "step_success_rate",
      "error_count"
    ],
    alerts: [
      {
        condition: "workflow_duration > 300s"
        action: "notify_admin"
        message: "工作流执行时间过长"
      },
      {
        condition: "error_count > 5"
        action: "notify_admin"
        message: "工作流错误次数过多"
      }
    ]
  }
}
```

## 3. 1关键元素

- workflow：工作流声明
- description：描述信息
- version：版本号
- author：作者
- inputs：输入参数
- outputs：输出参数
- variables：工作流变量
- steps：工作流步骤
- error_handling：错误处理
- monitoring：监控配置

## 4. 1高级用法

### 4.1 1并行执行与条件分支

```dsl
workflow "complex_order_processing" {
  description: "复杂订单处理工作流"
  version: "1.0.0"
  
  inputs: [
    { name: "order_id", type: "int", required: true },
    { name: "user_id", type: "int", required: true },
    { name: "items", type: "array<OrderItem>", required: true }
  ]
  
  outputs: [
    { name: "order_status", type: "string" },
    { name: "processing_result", type: "object" }
  ]
  
  variables: [
    { name: "total_amount", type: "decimal" },
    { name: "discount_amount", type: "decimal" },
    { name: "final_amount", type: "decimal" }
  ]
  
  steps: [
    {
      name: "validate_order"
      type: "task"
      action: "validate_order_data"
      inputs: ["order_id", "user_id", "items"]
      outputs: ["validation_result"]
    },
    {
      name: "parallel_processing"
      type: "parallel"
      branches: [
        {
          name: "inventory_check"
          steps: [
            {
              name: "check_inventory"
              type: "task"
              action: "check_inventory_availability"
              inputs: ["items"]
              outputs: ["inventory_status"]
            }
          ]
        },
        {
          name: "user_analysis"
          steps: [
            {
              name: "analyze_user"
              type: "task"
              action: "analyze_user_behavior"
              inputs: ["user_id"]
              outputs: ["user_analysis"]
            },
            {
              name: "calculate_discount"
              type: "task"
              action: "calculate_user_discount"
              inputs: ["user_analysis"]
              outputs: ["discount_amount"]
            }
          ]
        }
      ]
      condition: "validation_result.success == true"
    },
    {
      name: "conditional_processing"
      type: "conditional"
      condition: "inventory_status.available == true AND discount_amount > 0"
      true_branch: [
        {
          name: "apply_discount"
          type: "task"
          action: "apply_discount_to_order"
          inputs: ["discount_amount"]
          outputs: ["final_amount"]
        }
      ],
      false_branch: [
        {
          name: "use_original_amount"
          type: "task"
          action: "set_final_amount"
          inputs: ["total_amount"]
          outputs: ["final_amount"]
        }
      ]
    },
    {
      name: "process_payment"
      type: "task"
      action: "process_payment"
      inputs: ["final_amount", "user_id"]
      outputs: ["payment_status"]
      condition: "final_amount > 0"
    }
  ]
  
  error_handling: {
    validation_error: {
      action: "return_error"
      message: "订单验证失败"
    },
    inventory_error: {
      action: "notify_user"
      message: "库存不足"
    },
    payment_error: {
      action: "rollback_and_notify"
      message: "支付失败"
    }
  }
}
```

### 4.2 1状态机与状态转换

```dsl
workflow "order_state_machine" {
  description: "订单状态机工作流"
  version: "1.0.0"
  
  inputs: [
    { name: "order_id", type: "int", required: true },
    { name: "action", type: "string", required: true }
  ]
  
  outputs: [
    { name: "new_state", type: "string" },
    { name: "state_changed", type: "boolean" }
  ]
  
  state_machine: {
    initial_state: "pending"
    states: [
      {
        name: "pending"
        allowed_actions: ["confirm", "cancel"]
        entry_actions: ["notify_pending"]
        exit_actions: ["log_state_change"]
        transitions: [
          {
            action: "confirm"
            target: "confirmed"
            condition: "can_confirm_order(order_id)"
            actions: ["validate_order", "notify_confirmation"]
          },
          {
            action: "cancel"
            target: "cancelled"
            condition: "can_cancel_order(order_id)"
            actions: ["cancel_order", "notify_cancellation"]
          }
        ]
      },
      {
        name: "confirmed"
        allowed_actions: ["ship", "cancel"]
        entry_actions: ["prepare_shipping"]
        transitions: [
          {
            action: "ship"
            target: "shipped"
            condition: "inventory_available(order_id)"
            actions: ["prepare_shipment", "update_inventory"]
          },
          {
            action: "cancel"
            target: "cancelled"
            condition: "can_cancel_order(order_id)"
            actions: ["cancel_order", "restore_inventory"]
          }
        ]
      },
      {
        name: "shipped"
        allowed_actions: ["deliver", "return"]
        entry_actions: ["start_delivery_tracking"]
        transitions: [
          {
            action: "deliver"
            target: "delivered"
            condition: "delivery_confirmed(order_id)"
            actions: ["complete_delivery", "notify_delivery"]
          },
          {
            action: "return"
            target: "returned"
            condition: "return_requested(order_id)"
            actions: ["process_return", "notify_return"]
          }
        ]
      },
      {
        name: "delivered"
        allowed_actions: ["complete", "return"]
        entry_actions: ["start_completion_timer"]
        transitions: [
          {
            action: "complete"
            target: "completed"
            condition: "completion_confirmed(order_id)"
            actions: ["complete_order", "send_feedback_request"]
          },
          {
            action: "return"
            target: "returned"
            condition: "return_requested(order_id)"
            actions: ["process_return", "notify_return"]
          }
        ]
      },
      {
        name: "cancelled"
        allowed_actions: []
        entry_actions: ["process_cancellation"]
        final: true
      },
      {
        name: "returned"
        allowed_actions: ["refund"]
        entry_actions: ["process_return_request"]
        transitions: [
          {
            action: "refund"
            target: "refunded"
            condition: "refund_processed(order_id)"
            actions: ["process_refund", "notify_refund"]
          }
        ]
      },
      {
        name: "completed"
        allowed_actions: []
        entry_actions: ["finalize_order"]
        final: true
      },
      {
        name: "refunded"
        allowed_actions: []
        entry_actions: ["finalize_refund"]
        final: true
      }
    ]
  }
  
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
}
```

### 4.3 1循环与迭代处理

```dsl
workflow "batch_processing_workflow" {
  description: "批量处理工作流"
  version: "1.0.0"
  
  inputs: [
    { name: "batch_id", type: "int", required: true },
    { name: "items", type: "array<ProcessingItem>", required: true }
  ]
  
  outputs: [
    { name: "processing_results", type: "array<ProcessingResult>" },
    { name: "success_count", type: "int" },
    { name: "failure_count", type: "int" }
  ]
  
  variables: [
    { name: "current_index", type: "int", initial: 0 },
    { name: "results", type: "array<ProcessingResult>", initial: [] },
    { name: "success_count", type: "int", initial: 0 },
    { name: "failure_count", type: "int", initial: 0 }
  ]
  
  steps: [
    {
      name: "initialize_batch"
      type: "task"
      action: "initialize_batch_processing"
      inputs: ["batch_id"]
      outputs: ["batch_status"]
    },
    {
      name: "process_items_loop"
      type: "loop"
      condition: "current_index < items.length"
      steps: [
        {
          name: "process_current_item"
          type: "task"
          action: "process_single_item"
          inputs: ["items[current_index]"]
          outputs: ["processing_result"]
        },
        {
          name: "update_results"
          type: "task"
          action: "update_processing_results"
          inputs: ["processing_result"]
          outputs: ["results", "success_count", "failure_count"]
        },
        {
          name: "increment_index"
          type: "task"
          action: "increment_current_index"
          inputs: ["current_index"]
          outputs: ["current_index"]
        }
      ]
    },
    {
      name: "finalize_batch"
      type: "task"
      action: "finalize_batch_processing"
      inputs: ["batch_id", "results", "success_count", "failure_count"]
      outputs: ["final_results"]
    }
  ]
  
  error_handling: {
    item_processing_error: {
      action: "continue_with_next_item"
      message: "单个项目处理失败，继续处理下一个"
    },
    batch_error: {
      action: "rollback_batch"
      message: "批量处理失败，回滚所有操作"
    }
  }
}
```

### 4.4 1事件驱动工作流

```dsl
workflow "event_driven_order_workflow" {
  description: "事件驱动订单工作流"
  version: "1.0.0"
  
  inputs: [
    { name: "order_id", type: "int", required: true }
  ]
  
  outputs: [
    { name: "workflow_status", type: "string" }
  ]
  
  events: [
    {
      name: "order_created"
      source: "order_service"
      payload: {
        order_id: "int",
        user_id: "int",
        items: "array<OrderItem>"
      }
    },
    {
      name: "payment_processed"
      source: "payment_service"
      payload: {
        order_id: "int",
        payment_status: "string",
        amount: "decimal"
      }
    },
    {
      name: "inventory_updated"
      source: "inventory_service"
      payload: {
        order_id: "int",
        inventory_status: "string"
      }
    },
    {
      name: "shipping_started"
      source: "shipping_service"
      payload: {
        order_id: "int",
        tracking_number: "string"
      }
    }
  ]
  
  event_handlers: [
    {
      event: "order_created"
      actions: [
        {
          name: "validate_order"
          type: "task"
          action: "validate_order_data"
          inputs: ["order_id", "user_id", "items"]
          outputs: ["validation_result"]
        },
        {
          name: "trigger_parallel_checks"
          type: "parallel"
          branches: [
            {
              name: "inventory_check"
              steps: [
                {
                  name: "check_inventory"
                  type: "task"
                  action: "check_inventory_availability"
                  inputs: ["items"]
                  outputs: ["inventory_status"]
                }
              ]
            },
            {
              name: "payment_preparation"
              steps: [
                {
                  name: "prepare_payment"
                  type: "task"
                  action: "prepare_payment_processing"
                  inputs: ["order_id", "user_id"]
                  outputs: ["payment_preparation"]
                }
              ]
            }
          ]
        }
      ]
    },
    {
      event: "payment_processed"
      condition: "payment_status == 'success'"
      actions: [
        {
          name: "update_order_status"
          type: "task"
          action: "update_order_to_paid"
          inputs: ["order_id"]
          outputs: ["order_status"]
        },
        {
          name: "trigger_shipping"
          type: "task"
          action: "initiate_shipping_process"
          inputs: ["order_id"]
          outputs: ["shipping_initiated"]
        }
      ]
    },
    {
      event: "inventory_updated"
      condition: "inventory_status == 'reserved'"
      actions: [
        {
          name: "confirm_inventory"
          type: "task"
          action: "confirm_inventory_reservation"
          inputs: ["order_id"]
          outputs: ["inventory_confirmed"]
        }
      ]
    },
    {
      event: "shipping_started"
      actions: [
        {
          name: "update_tracking"
          type: "task"
          action: "update_order_tracking"
          inputs: ["order_id", "tracking_number"]
          outputs: ["tracking_updated"]
        },
        {
          name: "notify_customer"
          type: "task"
          action: "notify_customer_shipping"
          inputs: ["order_id", "tracking_number"]
          async: true
        }
      ]
    }
  ]
  
  timeout: {
    duration: "24h"
    action: "escalate_to_admin"
    message: "工作流执行超时"
  }
  
  error_handling: {
    event_processing_error: {
      action: "retry_with_backoff"
      max_retries: 3
      backoff: "exponential"
    },
    workflow_timeout: {
      action: "notify_admin"
      message: "工作流执行超时"
    }
  }
}
```

## 5. 1代码生成模板

### 5.1 1Java工作流生成

```java
// OrderProcessingWorkflow.java
public class OrderProcessingWorkflow {
    
    private final WorkflowEngine workflowEngine;
    private final OrderService orderService;
    private final InventoryService inventoryService;
    private final PaymentService paymentService;
    
    public OrderProcessingWorkflow(WorkflowEngine workflowEngine,
                                 OrderService orderService,
                                 InventoryService inventoryService,
                                 PaymentService paymentService) {
        this.workflowEngine = workflowEngine;
        this.orderService = orderService;
        this.inventoryService = inventoryService;
        this.paymentService = paymentService;
    }
    
    public WorkflowResult execute(OrderProcessingInput input) {
        WorkflowContext context = new WorkflowContext();
        context.setInput(input);
        
        try {
            // Step 1: Validate Order
            ValidationResult validationResult = validateOrder(input);
            if (!validationResult.isSuccess()) {
                return WorkflowResult.error("订单验证失败: " + validationResult.getMessage());
            }
            context.setVariable("validation_result", validationResult);
            
            // Step 2: Check Inventory
            InventoryStatus inventoryStatus = checkInventory(input.getItems());
            context.setVariable("inventory_status", inventoryStatus);
            
            if (!inventoryStatus.isAvailable()) {
                return WorkflowResult.error("库存不足");
            }
            
            // Step 3: Calculate Total
            BigDecimal totalAmount = calculateOrderTotal(input.getItems());
            context.setVariable("total_amount", totalAmount);
            
            // Step 4: Process Payment
            PaymentStatus paymentStatus = processPayment(totalAmount, input.getUserId());
            context.setVariable("payment_status", paymentStatus);
            
            if (!paymentStatus.isSuccess()) {
                return WorkflowResult.error("支付失败: " + paymentStatus.getMessage());
            }
            
            // Step 5: Update Inventory
            updateInventory(input.getItems());
            
            // Step 6: Send Confirmation (async)
            CompletableFuture.runAsync(() -> 
                sendOrderConfirmation(input.getUserId(), input.getOrderId())
            );
            
            return WorkflowResult.success("订单处理成功");
            
        } catch (Exception e) {
            return WorkflowResult.error("系统错误: " + e.getMessage());
        }
    }
    
    private ValidationResult validateOrder(OrderProcessingInput input) {
        return orderService.validateOrder(input.getOrderId(), input.getUserId(), input.getItems());
    }
    
    private InventoryStatus checkInventory(List<OrderItem> items) {
        return inventoryService.checkAvailability(items);
    }
    
    private BigDecimal calculateOrderTotal(List<OrderItem> items) {
        return items.stream()
                   .map(item -> item.getPrice().multiply(BigDecimal.valueOf(item.getQuantity())))
                   .reduce(BigDecimal.ZERO, BigDecimal::add);
    }
    
    private PaymentStatus processPayment(BigDecimal amount, int userId) {
        return paymentService.processPayment(amount, userId);
    }
    
    private void updateInventory(List<OrderItem> items) {
        inventoryService.updateLevels(items);
    }
    
    private void sendOrderConfirmation(int userId, int orderId) {
        // Async notification logic
    }
}
```

### 5.2 1Python工作流生成

```python
# order_processing_workflow.py
import asyncio
from typing import List, Dict, Any
from decimal import Decimal

class OrderProcessingWorkflow:
    
    def __init__(self, order_service, inventory_service, payment_service):
        self.order_service = order_service
        self.inventory_service = inventory_service
        self.payment_service = payment_service
    
    async def execute(self, order_id: int, user_id: int, items: List[Dict]) -> Dict[str, Any]:
        context = {
            'order_id': order_id,
            'user_id': user_id,
            'items': items,
            'variables': {}
        }
        
        try:
            # Step 1: Validate Order
            validation_result = await self.validate_order(order_id, user_id, items)
            if not validation_result['success']:
                return {'status': 'error', 'message': f"订单验证失败: {validation_result['message']}"}
            
            context['variables']['validation_result'] = validation_result
            
            # Step 2: Check Inventory
            inventory_status = await self.check_inventory(items)
            context['variables']['inventory_status'] = inventory_status
            
            if not inventory_status['available']:
                return {'status': 'error', 'message': '库存不足'}
            
            # Step 3: Calculate Total
            total_amount = self.calculate_order_total(items)
            context['variables']['total_amount'] = total_amount
            
            # Step 4: Process Payment
            payment_status = await self.process_payment(total_amount, user_id)
            context['variables']['payment_status'] = payment_status
            
            if not payment_status['success']:
                return {'status': 'error', 'message': f"支付失败: {payment_status['message']}"}
            
            # Step 5: Update Inventory
            await self.update_inventory(items)
            
            # Step 6: Send Confirmation (async)
            asyncio.create_task(self.send_order_confirmation(user_id, order_id))
            
            return {
                'status': 'success',
                'message': '订单处理成功',
                'order_status': 'confirmed',
                'processing_result': {
                    'total_amount': total_amount,
                    'payment_status': payment_status['status']
                }
            }
            
        except Exception as e:
            return {'status': 'error', 'message': f"系统错误: {str(e)}"}
    
    async def validate_order(self, order_id: int, user_id: int, items: List[Dict]) -> Dict[str, Any]:
        return await self.order_service.validate_order(order_id, user_id, items)
    
    async def check_inventory(self, items: List[Dict]) -> Dict[str, Any]:
        return await self.inventory_service.check_availability(items)
    
    def calculate_order_total(self, items: List[Dict]) -> Decimal:
        total = Decimal('0')
        for item in items:
            total += Decimal(str(item['price'])) * Decimal(str(item['quantity']))
        return total
    
    async def process_payment(self, amount: Decimal, user_id: int) -> Dict[str, Any]:
        return await self.payment_service.process_payment(amount, user_id)
    
    async def update_inventory(self, items: List[Dict]):
        await self.inventory_service.update_levels(items)
    
    async def send_order_confirmation(self, user_id: int, order_id: int):
        # Async notification logic
        pass
```

### 5.3 1JavaScript工作流生成

```javascript
// orderProcessingWorkflow.js
class OrderProcessingWorkflow {
    
    constructor(orderService, inventoryService, paymentService) {
        this.orderService = orderService;
        this.inventoryService = inventoryService;
        this.paymentService = paymentService;
    }
    
    async execute(orderId, userId, items) {
        const context = {
            orderId,
            userId,
            items,
            variables: {}
        };
        
        try {
            // Step 1: Validate Order
            const validationResult = await this.validateOrder(orderId, userId, items);
            if (!validationResult.success) {
                return {
                    status: 'error',
                    message: `订单验证失败: ${validationResult.message}`
                };
            }
            context.variables.validationResult = validationResult;
            
            // Step 2: Check Inventory
            const inventoryStatus = await this.checkInventory(items);
            context.variables.inventoryStatus = inventoryStatus;
            
            if (!inventoryStatus.available) {
                return {
                    status: 'error',
                    message: '库存不足'
                };
            }
            
            // Step 3: Calculate Total
            const totalAmount = this.calculateOrderTotal(items);
            context.variables.totalAmount = totalAmount;
            
            // Step 4: Process Payment
            const paymentStatus = await this.processPayment(totalAmount, userId);
            context.variables.paymentStatus = paymentStatus;
            
            if (!paymentStatus.success) {
                return {
                    status: 'error',
                    message: `支付失败: ${paymentStatus.message}`
                };
            }
            
            // Step 5: Update Inventory
            await this.updateInventory(items);
            
            // Step 6: Send Confirmation (async)
            setImmediate(() => this.sendOrderConfirmation(userId, orderId));
            
            return {
                status: 'success',
                message: '订单处理成功',
                orderStatus: 'confirmed',
                processingResult: {
                    totalAmount,
                    paymentStatus: paymentStatus.status
                }
            };
            
        } catch (error) {
            return {
                status: 'error',
                message: `系统错误: ${error.message}`
            };
        }
    }
    
    async validateOrder(orderId, userId, items) {
        return await this.orderService.validateOrder(orderId, userId, items);
    }
    
    async checkInventory(items) {
        return await this.inventoryService.checkAvailability(items);
    }
    
    calculateOrderTotal(items) {
        return items.reduce((total, item) => {
            return total + (item.price * item.quantity);
        }, 0);
    }
    
    async processPayment(amount, userId) {
        return await this.paymentService.processPayment(amount, userId);
    }
    
    async updateInventory(items) {
        await this.inventoryService.updateLevels(items);
    }
    
    async sendOrderConfirmation(userId, orderId) {
        // Async notification logic
    }
}
```

## 6. 1验证规则

### 6.1 1语法验证规则

```yaml
validation:
  required_fields:
    - workflow.name
    - workflow.description
    - workflow.version
    - workflow.steps
  
  type_constraints:
    - field: "workflow.name"
      type: "string"
      pattern: "^[a-zA-Z_][a-zA-Z0-9_]*$"
    - field: "workflow.version"
      type: "string"
      pattern: "^[0-9]+\\.[0-9]+\\.[0-9]+$"
    - field: "workflow.steps"
      type: "array"
      min_items: 1
  
  business_rules:
    - rule: "workflow name must be unique"
    - rule: "all input parameters must be used in steps"
    - rule: "all output parameters must be set in steps"
    - rule: "step names must be unique within workflow"
```

### 6.2 1工作流验证规则

```yaml
workflow_validation:
  step_consistency:
    - rule: "steps must be in logical order"
    - rule: "all required inputs must be available before use"
    - rule: "output parameters must be set before return"
  
  state_machine_validation:
    - rule: "state machine must have valid initial state"
    - rule: "all states must have valid transitions"
    - rule: "final states must not have outgoing transitions"
  
  error_handling:
    - rule: "all error scenarios must be handled"
    - rule: "error messages must be user-friendly"
    - rule: "timeout mechanisms must be defined for long-running workflows"
```

## 7. 1最佳实践

### 7.1 1工作流设计模式

```dsl
# 线性处理模式
workflow "linear_processing" {
  description: "线性处理工作流"
  
  inputs: [
    { name: "data", type: "object", required: true }
  ]
  
  outputs: [
    { name: "result", type: "object" }
  ]
  
  steps: [
    {
      name: "step1"
      type: "task"
      action: "process_step1"
      inputs: ["data"]
      outputs: ["step1_result"]
    },
    {
      name: "step2"
      type: "task"
      action: "process_step2"
      inputs: ["step1_result"]
      outputs: ["step2_result"]
    },
    {
      name: "step3"
      type: "task"
      action: "process_step3"
      inputs: ["step2_result"]
      outputs: ["result"]
    }
  ]
}

# 并行处理模式
workflow "parallel_processing" {
  description: "并行处理工作流"
  
  inputs: [
    { name: "data", type: "object", required: true }
  ]
  
  outputs: [
    { name: "result", type: "object" }
  ]
  
  steps: [
    {
      name: "parallel_tasks"
      type: "parallel"
      branches: [
        {
          name: "branch1"
          steps: [
            {
              name: "task1"
              type: "task"
              action: "process_task1"
              inputs: ["data"]
              outputs: ["task1_result"]
            }
          ]
        },
        {
          name: "branch2"
          steps: [
            {
              name: "task2"
              type: "task"
              action: "process_task2"
              inputs: ["data"]
              outputs: ["task2_result"]
            }
          ]
        }
      ]
    },
    {
      name: "combine_results"
      type: "task"
      action: "combine_parallel_results"
      inputs: ["task1_result", "task2_result"]
      outputs: ["result"]
    }
  ]
}
```

### 7.2 1工作流命名规范

```dsl
# 推荐命名模式
workflow "entity_action_workflow" {
  # 实体_操作_工作流
}

workflow "process_entity_workflow" {
  # 处理_实体_工作流
}

workflow "entity_state_machine" {
  # 实体_状态机
}
```

## 8. 1与主流标准的映射

| DSL元素 | Apache Airflow | Temporal | Camunda | AWS Step Functions |
|---------|----------------|----------|---------|-------------------|
| workflow | dag | workflow | process | state machine |
| steps | tasks | activities | tasks | states |
| parallel | parallel | parallel | parallel gateway | parallel |
| conditional | branching | conditional | exclusive gateway | choice |
| loop | loop | loop | loop | map |
| error_handling | error handling | error handling | error handling | catch |

## 9. 1工程实践示例

```dsl
# 电商系统工作流示例
workflow "ecommerce_order_workflow" {
  description: "电商订单处理工作流"
  version: "1.0.0"
  author: "system"
  
  inputs: [
    { name: "order_id", type: "int", required: true },
    { name: "user_id", type: "int", required: true },
    { name: "items", type: "array<OrderItem>", required: true }
  ]
  
  outputs: [
    { name: "order_status", type: "string" },
    { name: "processing_result", type: "object" }
  ]
  
  variables: [
    { name: "total_amount", type: "decimal" },
    { name: "discount_amount", type: "decimal" },
    { name: "final_amount", type: "decimal" }
  ]
  
  steps: [
    {
      name: "validate_order"
      type: "task"
      action: "validate_order_data"
      inputs: ["order_id", "user_id", "items"]
      outputs: ["validation_result"]
      timeout: "30s"
      retry: {
        max_attempts: 3
        backoff: "exponential"
        initial_delay: "5s"
      }
    },
    {
      name: "parallel_checks"
      type: "parallel"
      branches: [
        {
          name: "inventory_check"
          steps: [
            {
              name: "check_inventory"
              type: "task"
              action: "check_inventory_availability"
              inputs: ["items"]
              outputs: ["inventory_status"]
            }
          ]
        },
        {
          name: "user_analysis"
          steps: [
            {
              name: "analyze_user"
              type: "task"
              action: "analyze_user_behavior"
              inputs: ["user_id"]
              outputs: ["user_analysis"]
            },
            {
              name: "calculate_discount"
              type: "task"
              action: "calculate_user_discount"
              inputs: ["user_analysis"]
              outputs: ["discount_amount"]
            }
          ]
        }
      ]
      condition: "validation_result.success == true"
    },
    {
      name: "calculate_total"
      type: "task"
      action: "calculate_order_total"
      inputs: ["items"]
      outputs: ["total_amount"]
      condition: "inventory_status.available == true"
    },
    {
      name: "apply_discount"
      type: "task"
      action: "apply_discount_to_order"
      inputs: ["total_amount", "discount_amount"]
      outputs: ["final_amount"]
      condition: "discount_amount > 0"
    },
    {
      name: "process_payment"
      type: "task"
      action: "process_payment"
      inputs: ["final_amount", "user_id"]
      outputs: ["payment_status"]
      condition: "final_amount > 0"
    },
    {
      name: "update_inventory"
      type: "task"
      action: "update_inventory_levels"
      inputs: ["items"]
      condition: "payment_status.success == true"
    },
    {
      name: "send_notifications"
      type: "parallel"
      branches: [
        {
          name: "customer_notification"
          steps: [
            {
              name: "send_order_confirmation"
              type: "task"
              action: "send_order_confirmation"
              inputs: ["user_id", "order_id"]
              async: true
            }
          ]
        },
        {
          name: "admin_notification"
          steps: [
            {
              name: "notify_admin"
              type: "task"
              action: "notify_admin_new_order"
              inputs: ["order_id", "final_amount"]
              async: true
            }
          ]
        }
      ]
      condition: "payment_status.success == true"
    }
  ]
  
  error_handling: {
    validation_error: {
      action: "return_error"
      message: "订单验证失败"
    },
    inventory_error: {
      action: "notify_user"
      message: "库存不足，订单无法处理"
    },
    payment_error: {
      action: "rollback_inventory"
      message: "支付失败，已回滚库存"
    },
    system_error: {
      action: "log_error_and_notify_admin"
      message: "系统错误，请联系管理员"
    }
  }
  
  monitoring: {
    metrics: [
      "workflow_duration",
      "step_success_rate",
      "error_count",
      "payment_success_rate"
    ],
    alerts: [
      {
        condition: "workflow_duration > 300s"
        action: "notify_admin"
        message: "工作流执行时间过长"
      },
      {
        condition: "payment_success_rate < 0.95"
        action: "notify_admin"
        message: "支付成功率过低"
      }
    ]
  }
}
```

这个DSL设计为工作流建模提供了完整的配置语言，支持从简单的线性流程到复杂的并行处理、状态机、事件驱动等各种工作流模式，同时保持了良好的可扩展性和可维护性。
